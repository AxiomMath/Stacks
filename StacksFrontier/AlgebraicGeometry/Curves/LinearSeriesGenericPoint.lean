module

public import StacksFrontier.AlgebraicGeometry.ProjectiveFromSections.Morphism
public import StacksFrontier.AlgebraicGeometry.ProjGlobalSectionsAppTop.Consumers
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The generic point of the morphism attached to a family of sections

Let `X` be a scheme, `ℒ` an invertible `𝒪_X`-module and `s₀, …, sₙ` global sections generating
`ℒ`, so that [Stacks, Tag 01ND] attaches to them a morphism
`φ = φ_{(ℒ, (s₀, …, sₙ))} : X ⟶ 𝐏ⁿ_ℤ`. This file computes `φ` at a point `x` at which `sᵢ` does
not vanish: the composite of `φ` with `Spec 𝒪_{X, x} ⟶ X` is the `𝒪_{X, x}`-point of `𝐏ⁿ`
whose homogeneous coordinates are the germs at `x` of the ratios `s_k / sᵢ`.

## Main definitions

* `AlgebraicGeometry.projectiveSpacePoint`: the `R`-point of `𝐏ⁿ_ℤ` with given homogeneous
  coordinates — a family in `R` spanning the unit ideal.

## Main results

* `AlgebraicGeometry.specMap_comp_projectiveSpacePoint`: an `R`-point of `𝐏ⁿ` composed with
  `Spec S ⟶ Spec R` is the `S`-point whose coordinates are the images of the coordinates.
* `AlgebraicGeometry.fromSpecStalk_comp_toProjectiveSpaceAtUniverse`: **the morphism of
  [Stacks, Tag 01ND] at a point**, as the point with the germs of the ratios as coordinates.
* `AlgebraicGeometry.appTop_fromSpecStalkOfMem_topIso_inv`: the pullback of a section of `𝒪_X`
  over `U` along `Spec 𝒪_{X, x} ⟶ U` is its germ at `x`.

## Implementation notes

The homogeneous coordinates of a point of projective space are sections of the structure sheaf,
and the construction consuming them is
`Stacks.SectionsToProjectiveSpace.toProjectiveSpaceAtUniverse`, which asks for a family in
`Γ(T, ⊤)` spanning the unit ideal. For `T = Spec R` that is a family in `R` through
`AlgebraicGeometry.Scheme.ΓSpecIso`, and `AlgebraicGeometry.projectiveSpacePoint` performs the
translation once, so that naturality in `R` can be stated for a ring homomorphism.

The ratios themselves are `Stacks.ProjectiveFromSections.ratio`, sections of `𝒪_X` over the
nonvanishing open `X_{sᵢ}`, and the chart morphism of Tag 01ND is built from their
open-subscheme spelling `Stacks.ProjectiveFromSections.chartRatio`. The passage from the chart to
the point is `appTop_fromSpecStalkOfMem_topIso_inv` together with naturality of the construction
in the source scheme, `Stacks.SectionsToProjectiveSpace.HasPullbackNaturality`.

## References

* [Stacks Project, Tag 01ND](https://stacks.math.columbia.edu/tag/01ND)
* [Stacks Project, Tag 01NE](https://stacks.math.columbia.edu/tag/01NE)
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.ProjectiveFromSections

universe u

namespace AlgebraicGeometry

/-! ### Points of projective space with given homogeneous coordinates -/

/-- A family in `R` spanning the unit ideal spans it again in `Γ(Spec R, ⊤)`. -/
theorem span_range_ΓSpecIso_inv {R : CommRingCat.{u}} {n : ℕ} (c : Fin (n + 1) → R)
    (hc : Ideal.span (Set.range c) = ⊤) :
    Ideal.span (Set.range fun i => (Scheme.ΓSpecIso R).inv (c i)) = ⊤ := by
  classical
  set ρ : R →+* Γ(Spec R, ⊤) := ConcreteCategory.hom (Scheme.ΓSpecIso R).inv with hρ
  have h1 : (1 : R) ∈ Ideal.span (Set.range c) := by rw [hc]; exact Submodule.mem_top
  obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.mp h1
  rw [Ideal.eq_top_iff_one]
  have hone : (1 : Γ(Spec R, ⊤)) = ∑ i, ρ (a i) * ρ (c i) := by
    rw [← map_one ρ, ← ha, map_sum]
    exact Finset.sum_congr rfl fun i _ => map_mul _ _ _
  rw [hone]
  exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

/-- **The `R`-point of `𝐏ⁿ_ℤ` with homogeneous coordinates `c`**, for a family `c` in `R`
spanning the unit ideal: the morphism of [Stacks, Tag 01ND] for the free module of rank one on
`Spec R` and the sections `c`. -/
@[ega "II 7.3.9" "partial"]
def projectiveSpacePoint {R : CommRingCat.{u}} {n : ℕ} (c : Fin (n + 1) → R)
    (hc : Ideal.span (Set.range c) = ⊤) : Spec R ⟶ projectiveSpaceAtUniverse.{u} n :=
  Stacks.SectionsToProjectiveSpace.toProjectiveSpaceAtUniverse
    (fun i => (Scheme.ΓSpecIso R).inv (c i)) (span_range_ΓSpecIso_inv c hc)

/-- Precomposing the morphism to projective space with `g` gives the one of any family whose
members are the pullbacks along `g` of the original sections. -/
private theorem comp_toProjectiveSpaceAtUniverse_eq {Y Z : Scheme.{u}} (g : Y ⟶ Z) {n : ℕ}
    (s : Fin (n + 1) → Γ(Z, ⊤)) (hs : Ideal.span (Set.range s) = ⊤)
    (t : Fin (n + 1) → Γ(Y, ⊤)) (ht : Ideal.span (Set.range t) = ⊤)
    (h : ∀ i, g.appTop (s i) = t i) :
    g ≫ Stacks.SectionsToProjectiveSpace.toProjectiveSpaceAtUniverse s hs =
      Stacks.SectionsToProjectiveSpace.toProjectiveSpaceAtUniverse t ht := by
  rw [Stacks.ProjGlobalSectionsAppTop.hasPullbackNaturality g s hs (by simpa only [h] using ht)]
  exact Stacks.SectionsToProjectiveSpace.toProjectiveSpaceAtUniverse_congr (funext h) _ _

/-- **An `R`-point of `𝐏ⁿ` read over an `R`-algebra** is the point whose coordinates are the
images of the original ones. -/
theorem specMap_comp_projectiveSpacePoint {R S : CommRingCat.{u}} (φ : R ⟶ S) {n : ℕ}
    (c : Fin (n + 1) → R) (hc : Ideal.span (Set.range c) = ⊤)
    (hφc : Ideal.span (Set.range fun i => φ (c i)) = ⊤) :
    Spec.map φ ≫ projectiveSpacePoint c hc = projectiveSpacePoint (fun i => φ (c i)) hφc := by
  have happ : ∀ x : R,
      (Spec.map φ).appTop ((Scheme.ΓSpecIso R).inv x) = (Scheme.ΓSpecIso S).inv (φ x) :=
    fun x => (ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality φ) x).symm
  rw [projectiveSpacePoint, projectiveSpacePoint]
  exact comp_toProjectiveSpaceAtUniverse_eq _ _ _ _ _ fun i => happ (c i)

/-! ### The pullback of a section along the map from the spectrum of a stalk -/

/-- **The pullback of a section of `𝒪_X` over `U` along `Spec 𝒪_{X, x} ⟶ U` is its germ at
`x`.** Both sides are the component at `⊤` of the canonical morphism to `Spec Γ(X, U)`, which
`AlgebraicGeometry.Scheme.Opens.fromSpecStalkOfMem_toSpecΓ` identifies with `Spec` of the germ
map. -/
theorem appTop_fromSpecStalkOfMem_topIso_inv {X : Scheme.{u}} (U : X.Opens) (x : X) (hxU : x ∈ U)
    (a : Γ(X, U)) :
    (U.fromSpecStalkOfMem x hxU).appTop (U.topIso.inv a) =
      (Scheme.ΓSpecIso (X.presheaf.stalk x)).inv (X.presheaf.germ U x hxU a) := by
  have key : U.topIso.inv ≫ (U.fromSpecStalkOfMem x hxU).appTop =
      X.presheaf.germ U x hxU ≫ (Scheme.ΓSpecIso (X.presheaf.stalk x)).inv := by
    rw [← Iso.cancel_iso_hom_left (Scheme.ΓSpecIso Γ(X, U)), Scheme.ΓSpecIso_inv_naturality,
      Iso.hom_inv_id_assoc, ← Category.assoc, ← Scheme.Opens.toSpecΓ_appTop,
      ← Scheme.Hom.comp_appTop]
    exact congrArg Scheme.Hom.appTop (Scheme.Opens.fromSpecStalkOfMem_toSpecΓ U x hxU)
  exact ConcreteCategory.congr_hom key a

/-! ### The morphism of Tag 01ND at a point -/

variable {X : Scheme.{u}} {L : X.Modules} [Stacks.Ample.IsInvertibleModule X L] {n : ℕ}

/-- The germs at `x` of the ratios `s_k / sᵢ` span the unit ideal of `𝒪_{X, x}`, because the
`i`-th of them is `1`. -/
theorem span_range_germ_ratio (s : Fin (n + 1) → Γ(L, ⊤)) {i : Fin (n + 1)} {x : X}
    (hx : x ∈ nvCover s i) :
    Ideal.span (Set.range fun k => X.presheaf.germ (nvCover s i) x hx (ratio s i k)) = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  have h : X.presheaf.germ (nvCover s i) x hx (ratio s i i) = 1 := by
    rw [ratio_self]; exact map_one _
  rw [← h]
  exact Ideal.subset_span ⟨i, rfl⟩

/-- **The morphism of [Stacks, Tag 01ND] at a point at which `sᵢ` does not vanish.** Composed
with `Spec 𝒪_{X, x} ⟶ X` it is the `𝒪_{X, x}`-point of `𝐏ⁿ` whose homogeneous coordinates are
the germs at `x` of the ratios `s_k / sᵢ`.

The morphism restricted to the chart `X_{sᵢ}` is the chart morphism of the ratios
(`Stacks.ProjectiveFromSections.ι_toProjectiveSpaceAtUniverse`); the map out of the spectrum of
the stalk factors through that chart, and naturality of the construction in the source scheme
turns the chart morphism into the point whose coordinates are the pulled-back ratios, which are
their germs. -/
theorem fromSpecStalk_comp_toProjectiveSpaceAtUniverse (s : Fin (n + 1) → Γ(L, ⊤))
    (hs : GeneratesStalks s) {i : Fin (n + 1)} {x : X} (hx : x ∈ nvCover s i) :
    X.fromSpecStalk x ≫ toProjectiveSpaceAtUniverse s hs =
      projectiveSpacePoint (fun k => X.presheaf.germ (nvCover s i) x hx (ratio s i k))
        (span_range_germ_ratio s hx) := by
  rw [← Scheme.Opens.fromSpecStalkOfMem_ι (nvCover s i) x hx, Category.assoc,
    ι_toProjectiveSpaceAtUniverse s hs i, chartHom, projectiveSpacePoint]
  exact comp_toProjectiveSpaceAtUniverse_eq _ _ _ _ _ fun k => by
    rw [chartRatio, appTop_fromSpecStalkOfMem_topIso_inv]

end AlgebraicGeometry

end
