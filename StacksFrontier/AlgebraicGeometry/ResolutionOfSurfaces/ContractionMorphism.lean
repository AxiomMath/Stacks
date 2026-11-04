module

public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurveTwistGenerators
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceModuli.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Projective
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.AmpleTwistingSheaf
public import StacksFrontier.AlgebraicGeometry.AmpleQuasiAffinePullback.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Contraction.ExistsContraction
public import StacksFrontier.AlgebraicGeometry.NodalContraction.Basic
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurveDivisorTwist
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The morphism to projective space contracting an exceptional curve

This file carries out the construction in the proof of [Stacks, Tag 0C2M]. Let `S = Spec R` with
`R` Noetherian, `f : X ⟶ S` proper, `E ⊆ X` an exceptional curve of the first kind and `ℒ` an
invertible `𝒪_X`-module of degree `m + 1 ≥ 1` on `E` with `H¹(X, ℒ(mE)) = 0`, together with an
immersion `ψ : X ⟶ ℙᴺ_S` over `S` with `ℒ ≅ ψ^* 𝒪(1)`.

Let `t₀, …, t_N` be the sections of `ℒ` pulled back from the coordinates, `s₀, …, s_N` their images
in `𝓜 = ℒ((m+1)E)` under multiplication by `1_E^{m+1}`, and `s_{N+1}` a section of `𝓜`
generating it along `E`. These generate `𝓜` and define `φ : X ⟶ ℙ^{N+1}_S` over `S`. Then:

* `φ` is proper and its target is Noetherian;
* `φ` maps `E` to a single point, since `E` lands in the affine chart `D₊(T_{N+1})` and
  `Γ(E, 𝒪_E)` is a field;
* `φ` is quasi-finite at every point off `E`: on the chart `X_{sⱼ}` (`j ≤ N`) the first `N + 1`
  coordinates of `φ` recover `ψ`, which is injective.

So [Stacks, Tag 0C2L] applies and the first factor `b : X ⟶ X'` of the Stein factorization of
`φ` is a contraction of `E`; the second factor `π` is integral, so `𝓜' = π^* 𝒪(1)` is ample on
`X'`, and `b^* 𝓜' ≅ φ^* 𝒪(1) ≅ 𝓜`.

## Main results

* `AlgebraicGeometry.ExceptionalCurveContraction.exists_contraction_of_immersion`: the
  contraction `b`, with `𝒪_{X'} ≅ b_* 𝒪_X` and an ample invertible `𝓜'` on `X'` with
  `b^* 𝓜' ≅ ℒ((m+1)E)`.

## References

* [Stacks Project, Tag 0C2M](https://stacks.math.columbia.edu/tag/0C2M)
* [Stacks Project, Tag 0C2L](https://stacks.math.columbia.edu/tag/0C2L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.ProjectiveFromSections Stacks.TwistPullbackPinned Stacks.ProjectiveSpaceModuli
open Stacks.SectionsToProjectiveSpace Stacks.AmpleProjectiveImmersion
open RingedSpaceModuleAdjunction (modulePullback)

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] AlgebraicGeometry.projectiveSpaceAtUniverse

universe u

namespace AlgebraicGeometry.ExceptionalCurveContraction

/-! ### Coordinates transported along an isomorphism -/

section Transport

variable {X : Scheme.{u}} {N : ℕ} {A : X.Modules} [Stacks.Ample.IsInvertibleModule X A]
  (g : X ⟶ projectiveSpaceAtUniverse.{u} N)
  (β : (Scheme.Modules.pullback g).obj (twistingSheafAtUniverse.{u} N) ≅ A)

/-- The coordinates `g^* Tⱼ`, carried to `A` along `β : g^* 𝒪(1) ≅ A`. -/
def transportedCoords (j : Fin (N + 1)) : Γ(A, ⊤) :=
  Scheme.Modules.Hom.app β.hom ⊤ (pullbackCoordSection.{u} g j)

/-- The `j`-th transported coordinate does not vanish exactly on `g⁻¹ D₊(Tⱼ)`. -/
theorem nvCover_transportedCoords (j : Fin (N + 1)) :
    nvCover (transportedCoords g β) j =
      g ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen (coordGrading.{u} N) (MvPolynomial.X j) := by
  rw [← nvOpen_pullbackCoordSection g j]
  refine Opens.ext ?_
  exact Stacks.Ample.nonvanishingLocus_congr β (pullbackCoordSection.{u} g j)

/-- The transported coordinates generate `A`. -/
theorem generatesStalks_transportedCoords : GeneratesStalks (transportedCoords g β) := by
  refine Stacks.AmpleImmersionReduction.generatesStalks_of_forall_exists_mem _ fun x => ?_
  have hint : ⨆ i : Fin (N + 1),
      AlgebraicGeometry.Proj.basicOpen (coordGrading.{u} N) (MvPolynomial.X i) = ⊤ :=
    AlgebraicGeometry.Proj.iSup_basicOpen_eq_top _ _
      (AlgebraicGeometry.projectiveSpaceOver.irrelevant_coordGrading_le_span_X N)
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hint.ge
    (show g.base x ∈ (⊤ : (projectiveSpaceAtUniverse.{u} N).Opens) from trivial))
  exact ⟨i, (nvCover_transportedCoords g β i).ge hi⟩

/-- `g` is pinned by the transported coordinates. -/
theorem pin_transportedCoords (j : Fin (N + 1)) :
    (nvCover (transportedCoords g β) j).ι ≫ g =
      toProjectiveSpaceAtUniverse (chartRatio (transportedCoords g β) j)
        (span_range_chartRatio _ j) :=
  pin_of_iso (pullbackCoordSection.{u} g) (transportedCoords g β) β (fun _ => rfl) g
    (taut_pin g) j

end Transport

/-! ### The generating family of `ℒ((m+1)E)` -/

section Family

variable {X : Scheme.{u}} {N : ℕ} (D : X.IdealSheafData)
  [Stacks.Divisors.IsEffectiveCartierDivisor D] (A : X.Modules)
  [Stacks.Ample.IsInvertibleModule X A] (m : ℕ) (t : Fin (N + 1) → Γ(A, ⊤))
  (s₀ : Γ(Stacks.Surfaces.divisorTwist D A (m + 1), ⊤))

/-- The sections `s₀, …, s_N, s_{N+1}` of `ℒ((m+1)E)`: the images of the `tⱼ`, followed by
`s₀`. -/
def twistFamily (i : Fin (N + 1 + 1)) : Γ(Stacks.Surfaces.divisorTwist D A (m + 1), ⊤) :=
  Fin.lastCases s₀
    (fun j => Scheme.Modules.Hom.app (Stacks.Surfaces.divisorTwistMap D A (m + 1)) ⊤ (t j)) i

instance isInvertibleModule_divisorTwist (j : ℕ) :
    Stacks.Ample.IsInvertibleModule X (Stacks.Surfaces.divisorTwist D A j) :=
  Stacks.Surfaces.isInvertible_divisorTwist D A j

omit [Stacks.Divisors.IsEffectiveCartierDivisor D] [Stacks.Ample.IsInvertibleModule X A] in
theorem twistFamily_castSucc (j : Fin (N + 1)) :
    twistFamily D A m t s₀ j.castSucc =
      Scheme.Modules.Hom.app (Stacks.Surfaces.divisorTwistMap D A (m + 1)) ⊤ (t j) := by
  simp [twistFamily]

omit [Stacks.Divisors.IsEffectiveCartierDivisor D] [Stacks.Ample.IsInvertibleModule X A] in
theorem twistFamily_last : twistFamily D A m t s₀ (Fin.last _) = s₀ := by
  simp [twistFamily]

/-- The chart of `sⱼ` (`j ≤ N`) is the chart of `tⱼ` with `E` removed. -/
theorem nvCover_twistFamily_castSucc (j : Fin (N + 1)) :
    (nvCover (twistFamily D A m t s₀) j.castSucc : Set X) =
      (nvCover t j : Set X) ∩ (D.support : Set X)ᶜ := by
  show Stacks.Ample.nonvanishingLocus _ _ = Stacks.Ample.nonvanishingLocus _ _ ∩ _
  rw [twistFamily_castSucc]
  exact Stacks.Surfaces.nonvanishingLocus_divisorTwistMap D A (t j) (m + 1) (by omega)

/-- The family generates as soon as the `tⱼ` do and `s₀` generates along `E`. -/
theorem generatesStalks_twistFamily (ht : GeneratesStalks t)
    (hs₀ : ∀ x ∈ D.support, x ∈ nvOpen _ s₀) :
    GeneratesStalks (twistFamily D A m t s₀) := by
  refine Stacks.AmpleImmersionReduction.generatesStalks_of_forall_exists_mem _ fun x => ?_
  by_cases hx : x ∈ D.support
  · refine ⟨Fin.last _, ?_⟩
    show x ∈ nvOpen _ (twistFamily D A m t s₀ (Fin.last _))
    rw [twistFamily_last]
    exact hs₀ x hx
  · obtain ⟨j, hj⟩ := exists_mem_nvCover_of_generatesStalks t ht x
    refine ⟨j.castSucc, ?_⟩
    show x ∈ (nvCover (twistFamily D A m t s₀) j.castSucc : Set X)
    rw [nvCover_twistFamily_castSucc]
    exact ⟨hj, hx⟩

end Family


/-! ### The first `N + 1` coordinates of `φ` on a chart -/

section Chart

/-- `Tⱼ/Tⱼ = 1`. -/
theorem coordFrac_self {n : ℕ} (j : Fin (n + 1)) : coordFrac.{u} j j = 1 := by
  apply HomogeneousLocalization.val_injective
  rw [coordFrac, HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_one]
  simp

/-- Morphisms of equal families of sections spanning the unit ideal agree. -/
theorem toProjectiveSpaceAtUniverse_congr {V : Scheme.{u}} {n : ℕ} {b b' : Fin (n + 1) → Γ(V, ⊤)}
    (h : b = b') (hb : Ideal.span (Set.range b) = ⊤) (hb' : Ideal.span (Set.range b') = ⊤) :
    toProjectiveSpaceAtUniverse b hb = toProjectiveSpaceAtUniverse b' hb' := by
  subst h; rfl

variable {N : ℕ}

/-- The chart `D₊(Tⱼ)` of `ℙ^{N+1}_ℤ`, for `j ≤ N`. -/
abbrev chartOpen (j : Fin (N + 1)) : (projectiveSpaceAtUniverse.{u} (N + 1)).Opens :=
  AlgebraicGeometry.Proj.basicOpen (coordGrading.{u} (N + 1)) (MvPolynomial.X j.castSucc)

/-- The fractions `T₀/Tⱼ, …, T_N/Tⱼ` on the chart `D₊(Tⱼ)` of `ℙ^{N+1}_ℤ`: the linear projection
from the last coordinate point, read on that chart. -/
def chartCoords (j : Fin (N + 1)) (k : Fin (N + 1)) : Γ((chartOpen j).toScheme, ⊤) :=
  (chartOpen j).topIso.inv
    ((AlgebraicGeometry.Proj.awayToSection (coordGrading.{u} (N + 1))
      (MvPolynomial.X j.castSucc)).hom (coordFrac.{u} j.castSucc k.castSucc))

theorem span_range_chartCoords (j : Fin (N + 1)) :
    Ideal.span (Set.range (chartCoords.{u} j)) = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  refine Ideal.subset_span ⟨j, ?_⟩
  rw [chartCoords, coordFrac_self, map_one, map_one]

/-- The linear projection `D₊(Tⱼ) ⟶ ℙᴺ_ℤ` forgetting the last coordinate. -/
def chartProjection (j : Fin (N + 1)) :
    (chartOpen.{u} j).toScheme ⟶ projectiveSpaceAtUniverse.{u} N :=
  toProjectiveSpaceAtUniverse (chartCoords j) (span_range_chartCoords j)

variable {X : Scheme.{u}} (D : X.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor D]
  {A : X.Modules} [Stacks.Ample.IsInvertibleModule X A] (m : ℕ)
  (gψ : X ⟶ projectiveSpaceAtUniverse.{u} N)
  (βψ : (Scheme.Modules.pullback gψ).obj (twistingSheafAtUniverse.{u} N) ≅ A)
  (g : X ⟶ projectiveSpaceAtUniverse.{u} (N + 1))
  (β : (Scheme.Modules.pullback g).obj (twistingSheafAtUniverse.{u} (N + 1)) ≅
    Stacks.Surfaces.divisorTwist D A (m + 1))
  (hs : ∀ k : Fin (N + 1), transportedCoords g β k.castSucc =
    Scheme.Modules.Hom.app (Stacks.Surfaces.divisorTwistMap D A (m + 1)) ⊤
      (transportedCoords gψ βψ k))

include hs in
/-- The chart of `sⱼ` lies in the chart of `tⱼ`. -/
theorem nvCover_castSucc_le (j : Fin (N + 1)) :
    nvCover (transportedCoords g β) j.castSucc ≤ nvCover (transportedCoords gψ βψ) j := by
  intro x hx
  have h : x ∈ Stacks.Ample.nonvanishingLocus _
      (Scheme.Modules.Hom.app (Stacks.Surfaces.divisorTwistMap D A (m + 1)) ⊤
        (transportedCoords gψ βψ j)) := by
    rw [← hs j]; exact hx
  rw [Stacks.Surfaces.nonvanishingLocus_divisorTwistMap D A _ (m + 1) (by omega)] at h
  exact h.1

include hs in
/-- Off `E`, the chart of `tⱼ` is the chart of `sⱼ`. -/
theorem mem_nvCover_castSucc (j : Fin (N + 1)) {x : X}
    (hx : x ∈ nvCover (transportedCoords gψ βψ) j) (hxE : x ∉ D.support) :
    x ∈ nvCover (transportedCoords g β) j.castSucc := by
  show x ∈ Stacks.Ample.nonvanishingLocus _ _
  rw [hs j, Stacks.Surfaces.nonvanishingLocus_divisorTwistMap D A _ (m + 1) (by omega)]
  exact ⟨hx, hxE⟩

include hs in
/-- **On the chart `X_{sⱼ}` the ratios `sₖ/sⱼ` (`k ≤ N`) are the ratios `tₖ/tⱼ`**: multiplication
by `1_E^{m+1}` is linear. -/
theorem ratio_castSucc (j k : Fin (N + 1)) :
    ratio (transportedCoords g β) j.castSucc k.castSucc =
      resO (nvCover_castSucc_le D m gψ βψ g β hs j)
        (ratio (transportedCoords gψ βψ) j k) := by
  have hle := nvCover_castSucc_le D m gψ βψ g β hs j
  have hnat : ∀ y : Γ(A, ⊤),
      resT (nvCover (transportedCoords g β) j.castSucc)
          (Scheme.Modules.Hom.app (Stacks.Surfaces.divisorTwistMap D A (m + 1)) ⊤ y) =
        Scheme.Modules.Hom.app (Stacks.Surfaces.divisorTwistMap D A (m + 1))
          (nvCover (transportedCoords g β) j.castSucc)
          (resT (nvCover (transportedCoords g β) j.castSucc) y) := fun y =>
    (PresheafOfModules.naturality_apply (Stacks.Surfaces.divisorTwistMap D A (m + 1)).val
      (homOfLE (le_top : nvCover (transportedCoords g β) j.castSucc ≤ ⊤)).op y).symm
  have e1 := congrArg (resT (nvCover (transportedCoords g β) j.castSucc)) (hs j)
  have e2 := congrArg (resT (nvCover (transportedCoords g β) j.castSucc)) (hs k)
  refine (eq_div _ le_rfl ?_).symm
  rw [e1, e2, hnat, hnat, ← resO_ratio_smul (transportedCoords gψ βψ) hle k]
  exact (Scheme.Modules.Hom.app_smul _ _ _).symm

include hs in
/-- **On the chart `X_{sⱼ}`, the first `N + 1` coordinates of `φ` are `ψ`.** For any lift
`h' : X_{sⱼ} ⟶ D₊(Tⱼ)` of `g`, composing with the linear projection gives `ψ`. -/
theorem comp_chartProjection (j : Fin (N + 1))
    (h' : (nvCover (transportedCoords g β) j.castSucc).toScheme ⟶ (chartOpen.{u} j).toScheme)
    (hh' : h' ≫ (chartOpen j).ι = (nvCover (transportedCoords g β) j.castSucc).ι ≫ g) :
    h' ≫ chartProjection j = (nvCover (transportedCoords g β) j.castSucc).ι ≫ gψ := by
  have hle := nvCover_castSucc_le D m gψ βψ g β hs j
  -- the right-hand side
  have hR : (nvCover (transportedCoords g β) j.castSucc).ι ≫ gψ = toProjectiveSpaceAtUniverse
      (fun k => (X.homOfLE hle).appTop (chartRatio (transportedCoords gψ βψ) j k))
      (span_range_comp _ _ (span_range_chartRatio (transportedCoords gψ βψ) j)) := by
    rw [← X.homOfLE_ι hle, Category.assoc, pin_transportedCoords gψ βψ j]
    exact Stacks.ProjGlobalSectionsAppTop.hasPullbackNaturality _ _ _ _
  -- the left-hand side
  have hL : h' ≫ chartProjection j = toProjectiveSpaceAtUniverse
      (fun k => h'.appTop (chartCoords j k))
      (span_range_comp _ _ (span_range_chartCoords j)) :=
    Stacks.ProjGlobalSectionsAppTop.hasPullbackNaturality _ _ _ _
  rw [hR, hL]
  refine toProjectiveSpaceAtUniverse_congr (funext fun k => ?_) _ _
  have e₁ : (⊤ : (chartOpen.{u} j).toScheme.Opens) ≤ (chartOpen j).ι ⁻¹ᵁ chartOpen j :=
    (Scheme.Opens.ι_preimage_self _).ge
  have hcomp := Scheme.Hom.appLE_comp_appLE h' (chartOpen j).ι (chartOpen j) ⊤ ⊤ e₁ le_top
  have hι : (chartOpen.{u} j).ι.appLE (chartOpen j) ⊤ e₁ = (chartOpen j).topIso.inv := by
    rw [Scheme.Opens.ι_appLE]; rfl
  rw [hι] at hcomp
  have h1 := CategoryTheory.ConcreteCategory.congr_hom hcomp
    ((AlgebraicGeometry.Proj.awayToSection (coordGrading.{u} (N + 1))
      (MvPolynomial.X j.castSucc)).hom (coordFrac.{u} j.castSucc k.castSucc))
  rw [CategoryTheory.ConcreteCategory.comp_apply] at h1
  have e₂ : (⊤ : (nvCover (transportedCoords g β) j.castSucc).toScheme.Opens) ≤
      toProjectiveSpaceAtUniverse (chartRatio (transportedCoords g β) j.castSucc)
        (span_range_chartRatio (transportedCoords g β) j.castSucc) ⁻¹ᵁ chartOpen j := by
    have hb := (congrArg
      (fun a => (nvCover (transportedCoords g β) j.castSucc).toScheme.basicOpen a)
      (chartRatio_self (transportedCoords g β) j.castSucc)).trans (Scheme.basicOpen_one _)
    rw [preimage_basicOpen (chartRatio (transportedCoords g β) j.castSucc)
        (span_range_chartRatio (transportedCoords g β) j.castSucc)]
    exact hb.ge
  have h0 : h'.appTop (chartCoords j k) = Scheme.Hom.appLE h' ⊤ ⊤ le_top
      ((chartOpen j).topIso.inv
        ((AlgebraicGeometry.Proj.awayToSection (coordGrading.{u} (N + 1))
          (MvPolynomial.X j.castSucc)).hom (coordFrac.{u} j.castSucc k.castSucc))) := by
    rw [chartCoords, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  rw [h0, h1, appLE_congr_hom (hh'.trans (pin_transportedCoords g β j.castSucc)) _ _ _ e₂,
    appLE_top_coordFrac (chartRatio (transportedCoords g β) j.castSucc) _ _ _
      (chartRatio_self (transportedCoords g β) j.castSucc) e₂]
  show (nvCover (transportedCoords g β) j.castSucc).topIso.inv
      (ratio (transportedCoords g β) j.castSucc k.castSucc) =
    (X.homOfLE hle).appTop ((nvCover (transportedCoords gψ βψ) j).topIso.inv
      (ratio (transportedCoords gψ βψ) j k))
  rw [ratio_castSucc D m gψ βψ g β hs j k, homOfLE_appTop_topIso_inv]

end Chart

/-! ### The morphism `φ` to `ℙ^{N+1}_S` -/

section Morphism

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) {n : ℕ}
  (g : X ⟶ projectiveSpaceAtUniverse.{u} n)

/-- The morphism `X ⟶ ℙⁿ_S` over `S = Spec R` with integral component `g`. -/
def liftOver : X ⟶ projectiveSpaceOver n (Spec (.of R)) :=
  pullback.lift f g (terminal.hom_ext _ _)

@[simp] theorem liftOver_fst : liftOver f g ≫ pullback.fst _ _ = f := pullback.lift_fst _ _ _

@[simp] theorem liftOver_snd : liftOver f g ≫ pullback.snd _ _ = g := pullback.lift_snd _ _ _

instance isNoetherian_projectiveSpaceOver [IsNoetherianRing R] (n : ℕ) :
    IsNoetherian (projectiveSpaceOver n (Spec (.of R))) := by
  have := isProper_projectiveSpaceOver n (Spec (.of R))
  have : LocallyOfFiniteType (projectiveSpaceOver n (Spec (.of R)) ↘ Spec (.of R)) :=
    inferInstance
  have : IsLocallyNoetherian (projectiveSpaceOver n (Spec (.of R))) :=
    LocallyOfFiniteType.isLocallyNoetherian (projectiveSpaceOver n (Spec (.of R)) ↘ Spec (.of R))
  have : CompactSpace (projectiveSpaceOver n (Spec (.of R))) :=
    QuasiCompact.compactSpace_of_compactSpace
      (projectiveSpaceOver n (Spec (.of R)) ↘ Spec (.of R))
  exact ⟨⟩

theorem isProper_liftOver [IsProper f] : IsProper (liftOver f g) := by
  have := isProper_projectiveSpaceOver n (Spec (.of R))
  have : IsSeparated (pullback.fst (terminal.from (Spec (.of R)))
      (terminal.from (projectiveSpaceAtUniverse.{u} n))) :=
    show IsSeparated (projectiveSpaceOver n (Spec (.of R)) ↘ Spec (.of R)) from inferInstance
  have : IsProper (liftOver f g ≫ pullback.fst _ _) := by rw [liftOver_fst]; infer_instance
  exact IsProper.of_comp (liftOver f g) (pullback.fst _ _)

/-- The preimage under `pullback.snd` of the chart `D₊(Tᵢ)` is an affine open of `ℙⁿ_S`. -/
theorem isAffineOpen_preimage_basicOpen (i : Fin (n + 1)) :
    IsAffineOpen ((pullback.snd (terminal.from (Spec (.of R)))
        (terminal.from (projectiveSpaceAtUniverse.{u} n))) ⁻¹ᵁ
      AlgebraicGeometry.Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i)) :=
  (AlgebraicGeometry.Proj.isAffineOpen_basicOpen _ _ (X_mem_coordGrading_one i)
    Nat.one_pos).preimage _

/-- A morphism into `X` whose image under `g` lies in `V` lifts through the preimage of `V` in
`ℙⁿ_S`. -/
private theorem exists_lift_liftOver_preimage {Z : Scheme.{u}} (u : Z ⟶ X)
    (V : (projectiveSpaceAtUniverse.{u} n).Opens) (hV : ∀ z, g.base (u.base z) ∈ V) :
    ∃ h : Z ⟶ ((pullback.snd (terminal.from (Spec (.of R)))
        (terminal.from (projectiveSpaceAtUniverse.{u} n))) ⁻¹ᵁ V).toScheme,
      h ≫ ((pullback.snd (terminal.from (Spec (.of R)))
        (terminal.from (projectiveSpaceAtUniverse.{u} n))) ⁻¹ᵁ V).ι = u ≫ liftOver f g := by
  have hrange : Set.range (u ≫ liftOver f g).base ⊆ Set.range ((pullback.snd
      (terminal.from (Spec (.of R))) (terminal.from (projectiveSpaceAtUniverse.{u} n))) ⁻¹ᵁ
        V).ι.base := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    show (pullback.snd (terminal.from (Spec (.of R)))
      (terminal.from (projectiveSpaceAtUniverse.{u} n))).base ((liftOver f g).base (u.base z)) ∈ V
    rw [← Scheme.Hom.comp_apply, liftOver_snd]
    exact hV z
  exact ⟨_, IsOpenImmersion.lift_fac _ _ hrange⟩

end Morphism


/-! ### Quasi-finiteness off `E`, and `E` going to a point -/

section Properties

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) {N : ℕ}
  (D : X.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor D]
  {A : X.Modules} [Stacks.Ample.IsInvertibleModule X A] (m : ℕ)
  (i : X ⟶ projectiveSpaceOver N (Spec (.of R))) [IsImmersion i]
  (hi : i ≫ pullback.fst _ _ = f)
  (βψ : (Scheme.Modules.pullback (i ≫ pullback.snd _ _)).obj (twistingSheafAtUniverse.{u} N) ≅ A)
  (g : X ⟶ projectiveSpaceAtUniverse.{u} (N + 1))
  (β : (Scheme.Modules.pullback g).obj (twistingSheafAtUniverse.{u} (N + 1)) ≅
    Stacks.Surfaces.divisorTwist D A (m + 1))
  (hs : ∀ k : Fin (N + 1), transportedCoords g β k.castSucc =
    Scheme.Modules.Hom.app (Stacks.Surfaces.divisorTwistMap D A (m + 1)) ⊤
      (transportedCoords (i ≫ pullback.snd _ _) βψ k))

include hi hs in
/-- **On the chart `X_{sⱼ}` (`j ≤ N`) the morphism `φ` is injective**: there the immersion `ψ`
factors through `φ` followed by the linear projection over `S`. -/
theorem injective_ι_comp_liftOver (j : Fin (N + 1)) :
    Function.Injective ((nvCover (transportedCoords g β) j.castSucc).ι ≫ liftOver f g).base := by
  set W := nvCover (transportedCoords g β) j.castSucc
  set P' := pullback (terminal.from (Spec (.of R)))
    (terminal.from (projectiveSpaceAtUniverse.{u} (N + 1)))
  set DS : P'.Opens := (pullback.snd (terminal.from (Spec (.of R)))
    (terminal.from (projectiveSpaceAtUniverse.{u} (N + 1)))) ⁻¹ᵁ chartOpen j
  have hW : W = g ⁻¹ᵁ chartOpen j := nvCover_transportedCoords g β j.castSucc
  obtain ⟨hS, hSfac⟩ : ∃ h : W.toScheme ⟶ DS.toScheme, h ≫ DS.ι = W.ι ≫ liftOver f g :=
    exists_lift_liftOver_preimage f g W.ι _ fun w => hW.le w.2
  set h' := hS ≫ ((pullback.snd (terminal.from (Spec (.of R)))
    (terminal.from (projectiveSpaceAtUniverse.{u} (N + 1)))) ∣_ chartOpen j)
  have hh' : h' ≫ (chartOpen j).ι = W.ι ≫ g := by
    simp only [h', Category.assoc, morphismRestrict_ι]
    rw [← Category.assoc, hSfac, Category.assoc, liftOver_snd]
  have hproj := comp_chartProjection D m (i ≫ pullback.snd _ _) βψ g β hs j h' hh'
  set Q : DS.toScheme ⟶ projectiveSpaceOver N (Spec (.of R)) :=
    pullback.lift (DS.ι ≫ pullback.fst _ _)
      (((pullback.snd (terminal.from (Spec (.of R)))
        (terminal.from (projectiveSpaceAtUniverse.{u} (N + 1)))) ∣_ chartOpen j) ≫
        chartProjection j) (terminal.hom_ext _ _)
  have hQ : hS ≫ Q = W.ι ≫ i := by
    refine pullback.hom_ext ?_ ?_
    · simp only [Q, Category.assoc, pullback.lift_fst]
      rw [← Category.assoc, hSfac, Category.assoc, liftOver_fst, hi]
    · simp only [Q, Category.assoc, pullback.lift_snd]
      rw [← Category.assoc, hproj]
  intro a b hab
  have h1 : DS.ι.base (hS.base a) = DS.ι.base (hS.base b) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hSfac]
    exact hab
  have h2 : hS.base a = hS.base b := DS.ι.isOpenEmbedding.injective h1
  have h3 : (W.ι ≫ i).base a = (W.ι ≫ i).base b := by
    rw [← hQ, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, h2]
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at h3
  exact W.ι.isOpenEmbedding.injective (i.isEmbedding.injective h3)

include hi hs in
/-- **`φ` is quasi-finite at every point off `E`.** -/
theorem quasiFiniteAt_liftOver [LocallyOfFiniteType f] (hβψ : GeneratesStalks
      (transportedCoords (i ≫ pullback.snd _ _) βψ))
    (x : X) (hx : x ∉ D.support) : quasiFiniteAt (liftOver f g) x := by
  have : LocallyOfFiniteType (liftOver f g ≫ pullback.fst _ _) := by
    rw [liftOver_fst]; infer_instance
  have hft : LocallyOfFiniteType (liftOver f g) :=
    locallyOfFiniteType_of_comp (liftOver f g) (pullback.fst _ _)
  refine And.intro (finiteTypeAt_of_locallyOfFiniteType _ x) ?_
  obtain ⟨j, hj⟩ := exists_mem_nvCover_of_generatesStalks _ hβψ x
  have hxW := mem_nvCover_castSucc D m (i ≫ pullback.snd _ _) βψ g β hs j hj hx
  set W := nvCover (transportedCoords g β) j.castSucc
  have : LocallyOfFiniteType (W.ι ≫ liftOver f g) := inferInstance
  have : LocallyQuasiFinite (W.ι ≫ liftOver f g) :=
    LocallyQuasiFinite.of_injective (injective_ι_comp_liftOver f D m i hi βψ g β hs j)
  have h := (W.ι ≫ liftOver f g).quasiFiniteAt (⟨x, hxW⟩ : W.toScheme)
  exact (Scheme.Hom.quasiFiniteAt_comp_iff_of_isOpenImmersion (f := W.ι) (g := liftOver f g)
    (x := (⟨x, hxW⟩ : W.toScheme))).mp h

end Properties

section Point

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) {n : ℕ}
  (D : X.IdealSheafData) (k : Type u) [Field k] (e : projectiveLineProj k ≅ D.subscheme)
  {M : X.Modules} [Stacks.Ample.IsInvertibleModule X M]
  (g : X ⟶ projectiveSpaceAtUniverse.{u} n)
  (β : (Scheme.Modules.pullback g).obj (twistingSheafAtUniverse.{u} n) ≅ M)

include e in
/-- **`φ` maps `E` to a single point** as soon as some coordinate does not vanish along `E`: then
`E` lands in an affine chart of `ℙⁿ_S`, and `Γ(E, 𝒪_E) = k` is a field. -/
theorem exists_forall_liftOver_eq (l : Fin (n + 1))
    (hl : ∀ z : D.subscheme, D.subschemeι.base z ∈ nvCover (transportedCoords g β) l) :
    ∃ y, ∀ z : D.subscheme, (liftOver f g).base (D.subschemeι.base z) = y := by
  have := isIntegral_subscheme_of_iso_projectiveLineProj D k e
  obtain ⟨z₀⟩ : Nonempty D.subscheme := inferInstance
  set DS := (pullback.snd (terminal.from (Spec (.of R)))
    (terminal.from (projectiveSpaceAtUniverse.{u} n))) ⁻¹ᵁ
      AlgebraicGeometry.Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X l)
  have hDS : IsAffineOpen DS := isAffineOpen_preimage_basicOpen l
  obtain ⟨hE, hEfac⟩ : ∃ h : D.subscheme ⟶ DS.toScheme, h ≫ DS.ι = D.subschemeι ≫ liftOver f g :=
    exists_lift_liftOver_preimage f g D.subschemeι _ fun z => by
      have h := hl z
      rwa [nvCover_transportedCoords g β l] at h
  refine ⟨(liftOver f g).base (D.subschemeι.base z₀), fun z => ?_⟩
  have hc := const_of_isField_sections
    (Scheme.IdealSheafData.isField_sections_subscheme_of_iso_projectiveLineProj D k e)
    (hE ≫ hDS.isoSpec.hom) z z₀
  have h1 : hE.base z = hE.base z₀ := by
    have := congrArg hDS.isoSpec.inv.base hc
    rwa [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Category.assoc,
      Iso.hom_inv_id, Category.comp_id] at this
  have h2 := congrArg DS.ι.base h1
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hEfac, Scheme.Hom.comp_apply,
    Scheme.Hom.comp_apply] at h2
  exact h2

end Point



/-! ### The degree on the exceptional curve -/

section Degree

variable {X : Scheme.{u}} {D : X.IdealSheafData} {k : Type u} [Field k]
  {e : projectiveLineProj k ≅ D.subscheme}

/-- **Every invertible module has a degree on the exceptional curve** ([Stacks, Tag 0BXJ]): its
restriction to `E ≅ 𝐏¹_k` is a twist `𝒪(n)`. -/
theorem exists_iso_twistingSheaf_pullback (A : X.Modules) [Stacks.Ample.IsInvertibleModule X A] :
    ∃ n : ℤ, Nonempty ((modulePullback e.hom.toLRSHom.toShHom).obj
        ((modulePullback D.subschemeι.toLRSHom.toShHom).obj A) ≅
      ProjectiveSpectrum.Proj.twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin 2) k) n) := by
  have h1 := Stacks.InvertiblePullback.isInvertibleModule_pullback D.subschemeι A
  have h2 := Stacks.InvertiblePullback.isInvertibleModule_pullback e.hom
    ((modulePullback D.subschemeι.toLRSHom.toShHom).obj A)
  have h3 := (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
    _ _ _).mpr h2
  exact Stacks.PicardUFD.exists_iso_twistingSheaf k _ h3

include e in
/-- The ring of global functions of the projective line is a field. -/
theorem isField_sections_projectiveLineProj : IsField Γ(projectiveLineProj k, ⊤) := by
  have hF := Scheme.IdealSheafData.isField_sections_subscheme_of_iso_projectiveLineProj D k e
  exact MulEquiv.isField hF
    (Scheme.Γ.mapIso e.op).commRingCatIsoToRingEquiv.symm.toMulEquiv

/-- The global sections of a negative twist on the projective line vanish. -/
@[sga "6 XIII 2.5" "special case"]
theorem subsingleton_sections_twistingSheaf_of_neg (k : Type u) [Field k] {d : ℤ} (hd : d < 0) :
    Subsingleton ((ProjectiveSpectrum.Proj.twistingSheaf
      (MvPolynomial.homogeneousSubmodule (Fin 2) k) d).val.obj (op ⊤)) := by
  have h : IsZero ((Stacks.Cohomology.sectionsFunctor (projectiveLineProj k) ⊤).obj
      (ProjectiveSpectrum.Proj.twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin 2) k) d)) :=
    IsZero.of_iso (Stacks.ProjectiveSpace.Cohomology.isZero_lineCohomology_zero_of_neg k hd)
      ((Functor.rightDerivedZeroIsoSelf
        (Stacks.Cohomology.sectionsFunctor (projectiveLineProj k) ⊤)).app _).symm
  exact ModuleCat.subsingleton_of_isZero h

include e in
/-- **The projective line has more than one point.** On a one-point scheme the local generator of
`𝒪(-1)` at the point generates over the whole space, so `Γ(𝐏¹, 𝒪(-1)) ≅ Γ(𝐏¹, 𝒪) = k ≠ 0`, while
`Γ(𝐏¹, 𝒪(-1)) = 0`. -/
theorem not_subsingleton_projectiveLineProj : ¬ Subsingleton (projectiveLineProj k) := by
  intro hsub
  have := isIntegral_subscheme_of_iso_projectiveLineProj D k e
  obtain ⟨z⟩ : Nonempty D.subscheme := inferInstance
  have hO := Stacks.PicardUFD.isInvertible_twistingSheaf k 1 (-1)
  obtain ⟨W, hpW, a, ha⟩ := @Stacks.SheafOfModules.exists_bijective_smul_of_isInvertible
    (projectiveLineProj k).toRingedSpace _ _ hO (e.inv.base z)
  have hW : W = ⊤ := eq_top_iff.mpr fun q _ => (Subsingleton.elim q (e.inv.base z)) ▸ hpW
  subst hW
  have hb := ha ⊤ le_rfl
  have hs := subsingleton_sections_twistingSheaf_of_neg k (d := -1) (by norm_num)
  have hF := (isField_sections_projectiveLineProj (e := e)).nontrivial
  obtain ⟨x, y, hxy⟩ := hF.exists_pair_ne
  exact hxy (hb.injective (@Subsingleton.elim _ hs _ _))

/-- The zero section vanishes everywhere. -/
theorem notMem_nonvanishingLocus_zero {Y : Scheme.{u}} (M : Y.Modules) (y : Y) :
    y ∉ Stacks.Ample.nonvanishingLocus M 0 := by
  rw [Stacks.Ample.mem_nonvanishingLocus_iff, not_not, map_zero]
  exact zero_mem _

/-- A nonzero global function on a scheme whose global functions form a field vanishes
nowhere. -/
theorem mem_nonvanishingLocus_of_isField {Y : Scheme.{u}} (hY : IsField Γ(Y, ⊤))
    (a : Γ(Stacks.Ample.unitModule Y, ⊤)) (ha : a ≠ 0) (y : Y) :
    y ∈ Stacks.Ample.nonvanishingLocus (Stacks.Ample.unitModule Y) a := by
  rw [Stacks.Ample.mem_nonvanishingLocus_iff]
  intro h
  have hmem := Stacks.Ample.mem_maximalIdeal_of_mem_maximalSmul Y y h
  rw [Stacks.Ample.unitStalkFun_Γgerm] at hmem
  let := hY.toField
  have hu : IsUnit (show Γ(Y, ⊤) from a) := isUnit_iff_ne_zero.mpr ha
  exact IsLocalRing.notMem_maximalIdeal.mpr (hu.map _) hmem

variable {R : Type u} [CommRing R] (f : X ⟶ Spec (.of R))

/-- **The degree on `E` of a module pulled back from an immersion into projective space is
positive.** If it were negative, the coordinate sections would all restrict to zero on `E`; if it
were zero, one of them would trivialise `ℒ` along `E`, so the immersion would carry `E` into an
affine chart and hence to a single point, while `E ≅ 𝐏¹` has more than one point. -/
theorem one_le_of_immersion (hE : D.IsExceptionalCurveOfFirstKind k e) (A : X.Modules)
    [Stacks.Ample.IsInvertibleModule X A] {N : ℕ} (i : X ⟶ projectiveSpaceOver N (Spec (.of R)))
    [IsImmersion i] (hi : i ≫ pullback.fst _ _ = f)
    (α : A ≅ (Scheme.Modules.pullback i).obj (projectiveSpaceTwistingSheaf N (Spec (.of R))))
    {m : ℤ} (hdeg : (modulePullback e.hom.toLRSHom.toShHom).obj
        ((modulePullback D.subschemeι.toLRSHom.toShHom).obj A) ≅
      ProjectiveSpectrum.Proj.twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin 2) k) m) :
    1 ≤ m := by
  have _hcart := hE.isEffectiveCartierDivisor
  have := isIntegral_subscheme_of_iso_projectiveLineProj D k e
  obtain ⟨z₀⟩ : Nonempty D.subscheme := inferInstance
  let βψ : (Scheme.Modules.pullback (i ≫ pullback.snd _ _)).obj
      (twistingSheafAtUniverse.{u} N) ≅ A :=
    ((Scheme.Modules.pullbackComp i (pullback.snd _ _)).app _).symm ≪≫ α.symm
  set t := transportedCoords (i ≫ pullback.snd _ _) βψ
  have ht := generatesStalks_transportedCoords (i ≫ pullback.snd _ _) βψ
  obtain ⟨j, hj⟩ := exists_mem_nvCover_of_generatesStalks t ht (D.subschemeι.base z₀)
  set N₁ := (modulePullback D.subschemeι.toLRSHom.toShHom).obj A
  have hN₁ : Stacks.Ample.IsInvertibleModule D.subscheme N₁ :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback D.subschemeι A
  set τ := Stacks.NonvanishingPullback.pullbackGlobalSection e.hom N₁
    (Stacks.NonvanishingPullback.pullbackGlobalSection D.subschemeι A (t j))
  have hτ : ∀ p, p ∈ Stacks.Ample.nonvanishingLocus _ τ ↔
      D.subschemeι.base (e.hom.base p) ∈ nvCover t j := fun p =>
    (Stacks.NonvanishingPullback.mem_nonvanishingLocus_pullback_iff e.hom N₁ _ p).trans
      (Stacks.NonvanishingPullback.mem_nonvanishingLocus_pullback_iff D.subschemeι A _ _)
  set σ := Scheme.Modules.Hom.app hdeg.hom ⊤ τ
  have hσ : ∀ p, p ∈ Stacks.Ample.nonvanishingLocus _ σ ↔
      D.subschemeι.base (e.hom.base p) ∈ nvCover t j := fun p => by
    rw [show σ = Scheme.Modules.Hom.app hdeg.hom ⊤ τ from rfl,
      Stacks.Ample.nonvanishingLocus_congr hdeg τ]
    exact hτ p
  have hinv : ∀ z, e.hom.base (e.inv.base z) = z := fun z => by
    rw [← Scheme.Hom.comp_apply, e.inv_hom_id]; rfl
  have hp₀ : e.inv.base z₀ ∈ Stacks.Ample.nonvanishingLocus _ σ := by
    rw [hσ, hinv]
    exact hj
  by_contra hm
  have hm' : m ≤ 0 := by omega
  rcases lt_or_eq_of_le hm' with hneg | hzero
  · have hs := subsingleton_sections_twistingSheaf_of_neg k hneg
    rw [show σ = 0 from @Subsingleton.elim _ hs _ _] at hp₀
    exact notMem_nonvanishingLocus_zero _ _ hp₀
  · subst hzero
    -- the coordinate `tⱼ` trivialises `ℒ` along `E`
    let T : ((modulePullback e.hom.toLRSHom.toShHom).obj N₁ : (projectiveLineProj k).Modules) ≅
        Stacks.Ample.unitModule (projectiveLineProj k) := by
      exact hdeg ≪≫ Stacks.AlgebraicGeometry.ProjEulerSequence.twistingSheafZeroIsoUnit
        (MvPolynomial.homogeneousSubmodule (Fin 2) k)
    set σ' : Γ(Stacks.Ample.unitModule (projectiveLineProj k), ⊤) :=
      Scheme.Modules.Hom.app T.hom ⊤ τ
    have hσ'τ : ∀ p, p ∈ Stacks.Ample.nonvanishingLocus _ σ' ↔
        p ∈ Stacks.Ample.nonvanishingLocus _ τ := fun p => by
      rw [show σ' = Scheme.Modules.Hom.app T.hom ⊤ τ from rfl,
        Stacks.Ample.nonvanishingLocus_congr T τ]
    have hσ' : σ' ≠ 0 := by
      intro h0
      have h1 : e.inv.base z₀ ∈ Stacks.Ample.nonvanishingLocus _ σ' := by
        rw [hσ'τ, hτ, hinv]
        exact hj
      rw [h0] at h1
      exact notMem_nonvanishingLocus_zero _ _ h1
    have hall : ∀ z : D.subscheme, D.subschemeι.base z ∈ nvCover t j := fun z => by
      have h1 := mem_nonvanishingLocus_of_isField (isField_sections_projectiveLineProj (e := e))
        σ' hσ' (e.inv.base z)
      rw [hσ'τ, hτ] at h1
      rwa [hinv] at h1
    -- so `E` goes to a single point
    have hil : i = liftOver f (i ≫ pullback.snd _ _) :=
      pullback.hom_ext (by rw [liftOver_fst, hi]) (by rw [liftOver_snd])
    obtain ⟨y, hy⟩ := exists_forall_liftOver_eq f D k e (i ≫ pullback.snd _ _) βψ j hall
    rw [← hil] at hy
    have hE1 : ∀ z : D.subscheme, z = z₀ := fun z =>
      D.subschemeι.isEmbedding.injective (i.isEmbedding.injective ((hy z).trans (hy z₀).symm))
    refine not_subsingleton_projectiveLineProj (e := e) ⟨fun p q => ?_⟩
    have hpq : e.hom.base p = e.hom.base q := (hE1 _).trans (hE1 _).symm
    have hinj : Function.Injective e.hom.base := e.hom.isEmbedding.injective
    exact hinj hpq

end Degree

/-! ### The contraction -/

section Contraction

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of R)) [IsProper f]
  {D : X.IdealSheafData} {k : Type u} [Field k] {e : projectiveLineProj k ≅ D.subscheme}

/-- **The contraction of an exceptional curve from an immersion into projective space.** Let
`f : X ⟶ Spec R` be proper with `R` Noetherian, `E ⊆ X` an exceptional curve of the first kind,
and `ℒ` an invertible `𝒪_X`-module of degree `m + 1` on `E` with `H¹(X, ℒ(mE)) = 0`, for which
there is an immersion `i : X ⟶ ℙᴺ_R` over `R` with `ℒ ≅ i^* 𝒪(1)`. Then there are a contraction
`b : X ⟶ X'` of `E`, with `𝒪_{X'} ≅ b_* 𝒪_X`, and an ample invertible `𝒪_{X'}`-module `𝓜'` with
`b^* 𝓜' ≅ ℒ((m+1)E)`.

This is the construction in the proof of [Stacks, Tag 0C2M]; the contraction is the first factor
of the Stein factorization of the morphism `X ⟶ ℙ^{N+1}_R` defined by the sections of
`ℒ((m+1)E)` described in the module docstring, via [Stacks, Tag 0C2L]. -/
theorem exists_contraction_of_immersion (hE : D.IsExceptionalCurveOfFirstKind k e)
    (A : X.Modules) [Stacks.Ample.IsInvertibleModule X A] (m : ℕ)
    (hdeg : (modulePullback e.hom.toLRSHom.toShHom).obj
        ((modulePullback D.subschemeι.toLRSHom.toShHom).obj A) ≅
      ProjectiveSpectrum.Proj.twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin 2) k) (m + 1))
    (hH1 : IsZero (((moduleGlobalSections X).rightDerived 1).obj
      (Stacks.Surfaces.divisorTwist D A m)))
    {N : ℕ} (i : X ⟶ projectiveSpaceOver N (Spec (.of R))) [IsImmersion i]
    (hi : i ≫ pullback.fst _ _ = f)
    (α : A ≅ (Scheme.Modules.pullback i).obj (projectiveSpaceTwistingSheaf N (Spec (.of R)))) :
    ∃ (X' : Scheme.{u}) (b : X ⟶ X') (_ : IsIso b.c) (M' : X'.Modules)
      (_ : Stacks.Ample.IsInvertibleModule X' M'),
      IsContractionOfExceptionalCurve D b ∧ Scheme.Modules.IsAmple X' M' ∧
        Nonempty ((Scheme.Modules.pullback b).obj M' ≅
          Stacks.Surfaces.divisorTwist D A (m + 1)) := by
  have _hcart := hE.isEffectiveCartierDivisor
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := ⟨⟩
  -- the coordinates of `ℒ`
  let βψ : (Scheme.Modules.pullback (i ≫ pullback.snd _ _)).obj
      (twistingSheafAtUniverse.{u} N) ≅ A :=
    ((Scheme.Modules.pullbackComp i (pullback.snd _ _)).app _).symm ≪≫ α.symm
  have ht := generatesStalks_transportedCoords (i ≫ pullback.snd _ _) βψ
  -- the section generating `ℒ((m+1)E)` along `E`
  obtain ⟨s₀, hs₀⟩ :=
    Stacks.Surfaces.exists_section_forall_mem_nonvanishingLocus_divisorTwist D k hE A m hdeg hH1
  have hs₀' : ∀ x ∈ D.support, x ∈ nvOpen _ s₀ := by
    intro x hx
    obtain ⟨z, rfl⟩ : x ∈ Set.range D.subschemeι := by
      rw [Scheme.IdealSheafData.range_subschemeι]; exact hx
    exact hs₀ z
  have hgen := generatesStalks_twistFamily D A m (transportedCoords (i ≫ pullback.snd _ _) βψ)
    s₀ ht hs₀'
  -- the morphism to `ℙ^{N+1}_ℤ`
  obtain ⟨g, α', hiso, hα'⟩ := exists_hom_and_iso_pullback_twistingSheafAtUniverse _ hgen
  let β : (Scheme.Modules.pullback g).obj (twistingSheafAtUniverse.{u} (N + 1)) ≅
      Stacks.Surfaces.divisorTwist D A (m + 1) := @asIso _ _ _ _ α' hiso
  have hsβ : transportedCoords g β = twistFamily D A m
      (transportedCoords (i ≫ pullback.snd _ _) βψ) s₀ := funext hα'
  have hs : ∀ k : Fin (N + 1), transportedCoords g β k.castSucc =
      Scheme.Modules.Hom.app (Stacks.Surfaces.divisorTwistMap D A (m + 1)) ⊤
        (transportedCoords (i ≫ pullback.snd _ _) βψ k) := fun k => by
    rw [hsβ, twistFamily_castSucc]
  -- `φ` and the hypotheses of Tag 0C2L
  have := isProper_liftOver f g
  obtain ⟨y, hy⟩ := exists_forall_liftOver_eq f D k e g β (Fin.last _) fun z => by
    show D.subschemeι.base z ∈ nvOpen _ (transportedCoords g β (Fin.last _))
    rw [hsβ, twistFamily_last]
    exact hs₀ z
  have hqf : ∀ x ∉ (D.support : Set X), quasiFiniteAt (liftOver f g) x := fun x hx =>
    quasiFiniteAt_liftOver f D m i hi βψ g β hs ht x hx
  obtain ⟨X', b, π, hbπ, hc, hπ, hb⟩ :=
    exists_isContractionOfExceptionalCurve_isSteinFactorization hE (liftOver f g) y hy hqf
  -- the ample module on `X'`
  let O₁ := projectiveSpaceTwistingSheaf (N + 1) (Spec (.of R))
  have : IsAffineHom π := inferInstance
  have hO₁ : Stacks.Ample.IsAmple _ O₁ :=
    Stacks.ProjectiveSpace.isAmple_projectiveSpaceTwistingSheaf (N + 1) (Spec (.of R))
  let M' := (modulePullback π.toLRSHom.toShHom).obj O₁
  have hM' : Stacks.Ample.IsInvertibleModule X' M' :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback π O₁
  have hamp : Stacks.Ample.IsAmple X' M' :=
    Stacks.AmpleQuasiAffinePullback.isAmple_modulePullback_of_isAffineHom π O₁ hO₁
  refine ⟨X', b, hc, M', hM', hb, Stacks.PowerFamilyBridge.modulesIsAmple_of_isAmple X' M' hamp,
    ⟨?_⟩⟩
  exact (Scheme.Modules.pullback b).mapIso
      ((Stacks.ProjectiveBundleQuotients.pullbackIso π).app O₁).symm ≪≫
    (Scheme.Modules.pullbackComp b π).app O₁ ≪≫
    (Scheme.Modules.pullbackCongr hbπ).app O₁ ≪≫
    (Scheme.Modules.pullbackComp (liftOver f g) (pullback.snd _ _)).app _ ≪≫
    (Scheme.Modules.pullbackCongr (liftOver_snd f g)).app _ ≪≫ β

end Contraction

end AlgebraicGeometry.ExceptionalCurveContraction

end
