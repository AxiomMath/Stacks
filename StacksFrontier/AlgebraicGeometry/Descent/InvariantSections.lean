module

public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Qcqs
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.DescentData
public import StacksFrontier.AlgebraicGeometry.AmplePowers.Basic
public import StacksFrontier.AlgebraicGeometry.NonvanishingPullback.Nonvanishing
public import Mathlib.CategoryTheory.Sites.Descent.IsPrestack

/-!
# Invariant sections through a nonvanishing point

Let `q : V ⟶ W` be a flat morphism of affine schemes, `π : X ⟶ V` a quasi-compact and
quasi-separated scheme over `V` and `F` a quasi-coherent `𝒪_X`-module. Let `X₂ = X ×_W V` with
its two projections `ρ₁, ρ₂ : X₂ ⟶ X` to `X` (the second one being a second presentation of
`X₂` as a base change of `X`), and let `κ : ρ₁^* F ≅ ρ₂^* F` be an isomorphism satisfying the
cocycle condition on a triple product `X₃`. A global section `m` of `F` is *invariant* when
`κ (ρ₁^* m) = ρ₂^* m`.

The main result says that the invariant sections generate `Γ(X, F)` at every point: if a global
section does not vanish at `x`, some invariant section does not vanish at `x`.

## Main definitions

* `Stacks.Descent.InvariantSections.IsInvariant`: invariance of a global section for `κ`.

## Main results

* `Stacks.Descent.InvariantSections.exists_isInvariant_mem_nonvanishingLocus`: an invariant
  section through every nonvanishing point.
* `AlgebraicGeometry.Scheme.Modules.pullHom_app_pullbackSection`: `pullHom` on a pulled-back
  global section.

## References

* [Stacks Project, Tag 023N](https://stacks.math.columbia.edu/tag/023N)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 0H78](https://stacks.math.columbia.edu/tag/0H78)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat (pullHom)
open Stacks.AlgebraicGeometry.SectionsBaseChange (le_preimage_top)

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- An isomorphism of modules is inverted on global sections. -/
private theorem app_top_inv_hom {Y : Scheme.{u}} {A B : Y.Modules} (e : A ≅ B) (x : Γ(A, ⊤)) :
    e.inv.app ⊤ (e.hom.app ⊤ x) = x := by
  change (e.hom ≫ e.inv).app ⊤ x = x
  rw [e.hom_inv_id]
  rfl

/-- **`pullHom` on a pulled-back global section.** The restriction along `g` of a morphism
`φ : f₁^* M ⟶ f₂^* N`, applied to the pullback of a global section `s` of `M` along the composite
`gf₁`, is the pullback along `g` of `φ (f₁^* s)`, carried to the pullback along the composite
`gf₂`. -/
theorem pullHom_app_pullbackSection {Y Y' Z₁ Z₂ : Scheme.{u}} {f₁ : Y ⟶ Z₁} {f₂ : Y ⟶ Z₂}
    {M : Z₁.Modules} {N : Z₂.Modules}
    (φ : (Scheme.Modules.pullback f₁).obj M ⟶ (Scheme.Modules.pullback f₂).obj N)
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ Z₁) (gf₂ : Y' ⟶ Z₂) (h₁ : g ≫ f₁ = gf₁) (h₂ : g ≫ f₂ = gf₂)
    (s : M.val.obj (op ⊤)) :
    (pullHom (F := modulePullbackPseudofunctor) φ g gf₁ gf₂ h₁ h₂).val.app (op ⊤)
        (pullbackSection gf₁ M ⊤ ⊤ (le_preimage_top gf₁ ⊤) s) =
      ((Scheme.Modules.pullbackCongr h₂).hom.app N).val.app (op ⊤)
        (((Scheme.Modules.pullbackComp g f₂).hom.app N).val.app (op ⊤)
          (pullbackSection g ((Scheme.Modules.pullback f₂).obj N) ⊤ ⊤ (le_preimage_top g ⊤)
            (φ.val.app (op ⊤) (pullbackSection f₁ M ⊤ ⊤ (le_preimage_top f₁ ⊤) s)))) := by
  subst h₁ h₂
  have hc := pullbackSection_comp g f₁ M ⊤ ⊤ ⊤ (le_preimage_top f₁ ⊤) (le_preimage_top g ⊤)
    (le_preimage_top (g ≫ f₁) ⊤) s
  have hinv : ((Scheme.Modules.pullbackComp g f₁).inv.app M).val.app (op ⊤)
      (pullbackSection (g ≫ f₁) M ⊤ ⊤ (le_preimage_top (g ≫ f₁) ⊤) s) =
      pullbackSection g ((Scheme.Modules.pullback f₁).obj M) ⊤ ⊤ (le_preimage_top g ⊤)
        (pullbackSection f₁ M ⊤ ⊤ (le_preimage_top f₁ ⊤) s) := by
    rw [← hc]
    exact app_top_inv_hom ((Scheme.Modules.pullbackComp g f₁).app M) _
  exact (congrArg (fun z ↦ ((Scheme.Modules.pullbackComp g f₂).hom.app N).val.app (op ⊤)
      (((Scheme.Modules.pullback g).map φ).val.app (op ⊤) z)) hinv).trans
    (congrArg (fun z ↦ ((Scheme.Modules.pullbackComp g f₂).hom.app N).val.app (op ⊤) z)
      (pullbackSection_naturality g φ ⊤ ⊤ (le_preimage_top g ⊤) _))

end AlgebraicGeometry.Scheme.Modules

namespace Stacks.Descent.InvariantSections

open Stacks.AlgebraicGeometry.SectionsBaseChange Stacks.FlatSectionsDescent
open Stacks.Ample (nonvanishingLocus)
open scoped TensorProduct

variable {W V X X₂ X₃ : Scheme.{u}} [IsAffine W] [IsAffine V] (q : V ⟶ W) [Flat q]
  (π : X ⟶ V) [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace X₂]
  [QuasiSeparatedSpace X₂] (F : X.Modules) [F.IsQuasicoherent]
  (ρ₁ ρ₂ : X₂ ⟶ X) (k₁ : X₂ ⟶ V) (sq₂ : IsPullback ρ₂ k₁ (π ≫ q) q)
  (hW : ρ₁ ≫ π ≫ q = ρ₂ ≫ π ≫ q)
  (κ : (Scheme.Modules.pullback ρ₁).obj F ≅ (Scheme.Modules.pullback ρ₂).obj F)

/-- A global section is **invariant** for `κ` when `κ` carries its pullback along `ρ₁` to its
pullback along `ρ₂`. -/
def IsInvariant (m : Γ(F, ⊤)) : Prop :=
  κ.hom.app ⊤ (pullbackSectionsHom ρ₁ F ⊤ ⊤ (le_preimage_top ρ₁ ⊤) m) =
    pullbackSectionsHom ρ₂ F ⊤ ⊤ (le_preimage_top ρ₂ ⊤) m

/-- The pullback of a global section is semilinear along the map of global functions. -/
theorem pullbackSectionsHom_top_smul {Y Z : Scheme.{u}} (p : Y ⟶ Z) (G : Z.Modules)
    (r : Γ(Z, ⊤)) (m : Γ(G, ⊤)) :
    pullbackSectionsHom p G ⊤ ⊤ (le_preimage_top p ⊤) (r • m) =
      (p.appLE ⊤ ⊤ (le_preimage_top p ⊤)).hom r •
        pullbackSectionsHom p G ⊤ ⊤ (le_preimage_top p ⊤) m := by
  rw [pullbackSectionsHom_top, pullbackSectionsHom_top, pullbackUnitSections_smul,
    Scheme.Hom.app_eq_appLE]
  rfl

/-- Pulling a global section back along a composite is pulling it back twice. -/
theorem pullbackComp_hom_app_pullbackSectionsHom {X' Y Z : Scheme.{u}} (f : X' ⟶ Y) (g : Y ⟶ Z)
    (M : Z.Modules) (s : Γ(M, ⊤)) :
    ((Scheme.Modules.pullbackComp f g).hom.app M).app ⊤
        (pullbackSectionsHom f ((Scheme.Modules.pullback g).obj M) ⊤ ⊤ (le_preimage_top f ⊤)
          (pullbackSectionsHom g M ⊤ ⊤ (le_preimage_top g ⊤) s)) =
      pullbackSectionsHom (f ≫ g) M ⊤ ⊤ (le_preimage_top (f ≫ g) ⊤) s :=
  Scheme.Modules.pullbackSection_comp f g M ⊤ ⊤ ⊤ _ _ _ s

/-- The inverse form of `pullbackComp_hom_app_pullbackSectionsHom`. -/
theorem pullbackComp_inv_app_pullbackSectionsHom {X' Y Z : Scheme.{u}} (f : X' ⟶ Y) (g : Y ⟶ Z)
    (M : Z.Modules) (s : Γ(M, ⊤)) :
    ((Scheme.Modules.pullbackComp f g).inv.app M).app ⊤
        (pullbackSectionsHom (f ≫ g) M ⊤ ⊤ (le_preimage_top (f ≫ g) ⊤) s) =
      pullbackSectionsHom f ((Scheme.Modules.pullback g).obj M) ⊤ ⊤ (le_preimage_top f ⊤)
        (pullbackSectionsHom g M ⊤ ⊤ (le_preimage_top g ⊤) s) := by
  rw [← pullbackComp_hom_app_pullbackSectionsHom f g M s]
  exact Scheme.Modules.app_top_inv_hom ((Scheme.Modules.pullbackComp f g).app M) _

/-- Pulling a global section back is compatible with an equality of morphisms. -/
theorem pullbackCongr_hom_app_pullbackSectionsHom {X' Z : Scheme.{u}} {f f' : X' ⟶ Z}
    (h : f = f') (M : Z.Modules) (s : Γ(M, ⊤)) :
    ((Scheme.Modules.pullbackCongr h).hom.app M).app ⊤
        (pullbackSectionsHom f M ⊤ ⊤ (le_preimage_top f ⊤) s) =
      pullbackSectionsHom f' M ⊤ ⊤ (le_preimage_top f' ⊤) s := by
  subst h
  rfl

/-- `pullHom` read on global sections, with source and target spelled as pullbacks. -/
def pullHomApp {Y Y' Z₁ Z₂ : Scheme.{u}} {f₁ : Y ⟶ Z₁} {f₂ : Y ⟶ Z₂}
    {M : Z₁.Modules} {N : Z₂.Modules}
    (φ : (Scheme.Modules.pullback f₁).obj M ⟶ (Scheme.Modules.pullback f₂).obj N)
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ Z₁) (gf₂ : Y' ⟶ Z₂) (h₁ : g ≫ f₁ = gf₁) (h₂ : g ≫ f₂ = gf₂) :
    Γ((Scheme.Modules.pullback gf₁).obj M, ⊤) ⟶ Γ((Scheme.Modules.pullback gf₂).obj N, ⊤) :=
  Scheme.Modules.Hom.app (M := (Scheme.Modules.pullback gf₁).obj M)
    (N := (Scheme.Modules.pullback gf₂).obj N)
    (pullHom (F := modulePullbackPseudofunctor) φ g gf₁ gf₂ h₁ h₂) ⊤

/-- `pullHom_app_pullbackSection` in the spelling of global sections. -/
theorem pullHomApp_pullbackSectionsHom {Y Y' Z₁ Z₂ : Scheme.{u}} {f₁ : Y ⟶ Z₁} {f₂ : Y ⟶ Z₂}
    {M : Z₁.Modules} {N : Z₂.Modules}
    (φ : (Scheme.Modules.pullback f₁).obj M ⟶ (Scheme.Modules.pullback f₂).obj N)
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ Z₁) (gf₂ : Y' ⟶ Z₂) (h₁ : g ≫ f₁ = gf₁) (h₂ : g ≫ f₂ = gf₂)
    (s : Γ(M, ⊤)) :
    pullHomApp φ g gf₁ gf₂ h₁ h₂ (pullbackSectionsHom gf₁ M ⊤ ⊤ (le_preimage_top gf₁ ⊤) s) =
      ((Scheme.Modules.pullbackCongr h₂).hom.app N).app ⊤
        (((Scheme.Modules.pullbackComp g f₂).hom.app N).app ⊤
          (pullbackSectionsHom g ((Scheme.Modules.pullback f₂).obj N) ⊤ ⊤ (le_preimage_top g ⊤)
            (φ.app ⊤ (pullbackSectionsHom f₁ M ⊤ ⊤ (le_preimage_top f₁ ⊤) s)))) :=
  Scheme.Modules.pullHom_app_pullbackSection φ g gf₁ gf₂ h₁ h₂ s

/-- `pullHomApp` is linear over the global functions. -/
theorem pullHomApp_smul {Y Y' Z₁ Z₂ : Scheme.{u}} {f₁ : Y ⟶ Z₁} {f₂ : Y ⟶ Z₂}
    {M : Z₁.Modules} {N : Z₂.Modules}
    (φ : (Scheme.Modules.pullback f₁).obj M ⟶ (Scheme.Modules.pullback f₂).obj N)
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ Z₁) (gf₂ : Y' ⟶ Z₂) (h₁ : g ≫ f₁ = gf₁) (h₂ : g ≫ f₂ = gf₂)
    (r : Γ(Y', ⊤)) (x : Γ((Scheme.Modules.pullback gf₁).obj M, ⊤)) :
    pullHomApp φ g gf₁ gf₂ h₁ h₂ (r • x) = r • pullHomApp φ g gf₁ gf₂ h₁ h₂ x :=
  Scheme.Modules.Hom.app_smul _ r x

/-- A relation `φ₁₂ ≫ φ₂₃ = φ₁₃` between `pullHom`s, read on global sections. -/
theorem pullHomApp_comp {Y Z : Scheme.{u}} {f₁ f₂ : Y ⟶ Z} {M : Z.Modules}
    (φ : (Scheme.Modules.pullback f₁).obj M ⟶ (Scheme.Modules.pullback f₂).obj M)
    {Y' : Scheme.{u}} (g₁₂ g₂₃ g₁₃ : Y' ⟶ Y) (t₁ t₂ t₃ : Y' ⟶ Z)
    (h₁₂₁ : g₁₂ ≫ f₁ = t₁) (h₁₂₂ : g₁₂ ≫ f₂ = t₂) (h₂₃₁ : g₂₃ ≫ f₁ = t₂)
    (h₂₃₂ : g₂₃ ≫ f₂ = t₃) (h₁₃₁ : g₁₃ ≫ f₁ = t₁) (h₁₃₂ : g₁₃ ≫ f₂ = t₃)
    (hcoc : pullHom (F := modulePullbackPseudofunctor) φ g₁₂ t₁ t₂ h₁₂₁ h₁₂₂ ≫
        pullHom (F := modulePullbackPseudofunctor) φ g₂₃ t₂ t₃ h₂₃₁ h₂₃₂ =
      pullHom (F := modulePullbackPseudofunctor) φ g₁₃ t₁ t₃ h₁₃₁ h₁₃₂)
    (x : Γ((Scheme.Modules.pullback t₁).obj M, ⊤)) :
    pullHomApp φ g₂₃ t₂ t₃ h₂₃₁ h₂₃₂ (pullHomApp φ g₁₂ t₁ t₂ h₁₂₁ h₁₂₂ x) =
      pullHomApp φ g₁₃ t₁ t₃ h₁₃₁ h₁₃₂ x := by
  have h := congrArg (fun ψ ↦ Scheme.Modules.Hom.app (M := (Scheme.Modules.pullback t₁).obj M)
    (N := (Scheme.Modules.pullback t₃).obj M) ψ ⊤ x) hcoc
  exact h

/-- The inverse form of `pullbackCongr_hom_app_pullbackSectionsHom`. -/
theorem pullbackCongr_inv_app_pullbackSectionsHom {X' Z : Scheme.{u}} {f f' : X' ⟶ Z}
    (h : f = f') (M : Z.Modules) (s : Γ(M, ⊤)) :
    ((Scheme.Modules.pullbackCongr h).inv.app M).app ⊤
        (pullbackSectionsHom f' M ⊤ ⊤ (le_preimage_top f' ⊤) s) =
      pullbackSectionsHom f M ⊤ ⊤ (le_preimage_top f ⊤) s := by
  subst h
  rfl

/-- A relation `φ₁ ≫ φ₂ = φ₃` between morphisms of modules, read on a global section. -/
theorem app_app_of_comp_eq {Y : Scheme.{u}} {A B C : Y.Modules} {φ₁ : A ⟶ B} {φ₂ : B ⟶ C}
    {φ₃ : A ⟶ C} (h : φ₁ ≫ φ₂ = φ₃) (x : Γ(A, ⊤)) : φ₂.app ⊤ (φ₁.app ⊤ x) = φ₃.app ⊤ x := by
  rw [← h]
  rfl

/-- A point lies in the nonvanishing locus of a pulled-back section exactly when its image lies in
that of the section (Stacks 0H78). -/
theorem mem_nonvanishingLocus_pullbackSectionsHom_iff {Y Z : Scheme.{u}} (p : Y ⟶ Z)
    (G : Z.Modules) (s : Γ(G, ⊤)) (y : Y) :
    y ∈ nonvanishingLocus ((Scheme.Modules.pullback p).obj G)
        (pullbackSectionsHom p G ⊤ ⊤ (le_preimage_top p ⊤) s) ↔
      p.base y ∈ nonvanishingLocus G s := by
  rw [show pullbackSectionsHom p G ⊤ ⊤ (le_preimage_top p ⊤) s =
      Stacks.NonvanishingPullback.pullbackGlobalSection p G s from pullbackSectionsHom_top p G s]
  exact Stacks.NonvanishingPullback.mem_nonvanishingLocus_pullback_iff p G s y

/-- Restricting a global section along two composable maps is restricting along the composite. -/
private theorem appLE_top_appLE_top_of_comp_eq {Y Y' Z : Scheme.{u}} {f : Y' ⟶ Y} {g : Y ⟶ Z}
    {h : Y' ⟶ Z} (e : f ≫ g = h) (a : Γ(Z, ⊤)) :
    (f.appLE ⊤ ⊤ (le_preimage_top f ⊤)).hom ((g.appLE ⊤ ⊤ (le_preimage_top g ⊤)).hom a) =
      (h.appLE ⊤ ⊤ (le_preimage_top h ⊤)).hom a := by
  subst e
  exact (appLE_comp_base g f ⊤ a).symm

/-- **A section of the base change of a submodule of sections that does not vanish at a point
comes from a member of the submodule not vanishing below it.** -/
theorem exists_mem_nonvanishingLocus_of_lTensor {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] {X Y : Scheme.{u}} (ρ : Y ⟶ X) (F : X.Modules) [Module R Γ(F, ⊤)]
    (K : Submodule R Γ(F, ⊤))
    (e : A ⊗[R] Γ(F, ⊤) →+ Γ((Scheme.Modules.pullback ρ).obj F, ⊤)) (c : A → Γ(Y, ⊤))
    (he : ∀ a m, e (a ⊗ₜ m) = c a • pullbackSectionsHom ρ F ⊤ ⊤ (le_preimage_top ρ ⊤) m)
    (z : A ⊗[R] K) (y : Y)
    (hy : y ∈ nonvanishingLocus _ (e (K.subtype.lTensor A z))) :
    ∃ m₀ ∈ K, ρ.base y ∈ nonvanishingLocus F m₀ := by
  induction z using TensorProduct.induction_on with
  | zero =>
    simp only [map_zero, Stacks.Ample.nonvanishingLocus_zero, Set.mem_empty_iff_false] at hy
  | tmul a m₀ =>
    rw [LinearMap.lTensor_tmul, he] at hy
    have hm' := Stacks.Ample.nonvanishingLocus_smul_subset _ (c a)
      (pullbackSectionsHom ρ F ⊤ ⊤ (le_preimage_top ρ ⊤) m₀.1) hy
    exact ⟨m₀.1, m₀.2, (mem_nonvanishingLocus_pullbackSectionsHom_iff ρ F m₀.1 y).mp hm'⟩
  | add w₁ w₂ h₁ h₂ =>
    rw [map_add, map_add] at hy
    rcases Stacks.Ample.nonvanishingLocus_add_subset _ _ _ hy with hy | hy
    · exact h₁ hy
    · exact h₂ hy

include sq₂ hW in
/-- **Invariant sections exist through every nonvanishing point.** -/
theorem exists_isInvariant_mem_nonvanishingLocus
    (Δ : X ⟶ X₂) (hΔ₁ : Δ ≫ ρ₁ = 𝟙 X) (hΔ₂ : Δ ≫ ρ₂ = 𝟙 X)
    (σ₁₂ σ₂₃ σ₁₃ : X₃ ⟶ X₂) (k₃ : X₃ ⟶ V) (sq₃ : IsPullback σ₂₃ k₃ (ρ₂ ≫ π ≫ q) q)
    (t₁ t₂ t₃ : X₃ ⟶ X) (h₁₂₁ : σ₁₂ ≫ ρ₁ = t₁) (h₁₂₂ : σ₁₂ ≫ ρ₂ = t₂)
    (h₂₃₁ : σ₂₃ ≫ ρ₁ = t₂) (h₂₃₂ : σ₂₃ ≫ ρ₂ = t₃) (h₁₃₁ : σ₁₃ ≫ ρ₁ = t₁)
    (h₁₃₂ : σ₁₃ ≫ ρ₂ = t₃) (hk₁₂ : σ₁₂ ≫ k₁ = k₃) (hk₁₃ : σ₁₃ ≫ k₁ = k₃)
    (hcoc : pullHom (F := modulePullbackPseudofunctor) κ.hom σ₁₂ t₁ t₂ h₁₂₁ h₁₂₂ ≫
        pullHom (F := modulePullbackPseudofunctor) κ.hom σ₂₃ t₂ t₃ h₂₃₁ h₂₃₂ =
      pullHom (F := modulePullbackPseudofunctor) κ.hom σ₁₃ t₁ t₃ h₁₃₁ h₁₃₂)
    (m : Γ(F, ⊤)) (x : X) (hx : x ∈ nonvanishingLocus F m) :
    ∃ m₀ : Γ(F, ⊤), x ∈ nonvanishingLocus F m₀ ∧ IsInvariant F ρ₁ ρ₂ κ m₀ := by
  classical
  let algRA : Algebra Γ(W, ⊤) Γ(V, ⊤) := baseAlgebra q
  have flatRA : Module.Flat Γ(W, ⊤) Γ(V, ⊤) :=
    Flat.flat_appLE q (isAffineOpen_top W) (isAffineOpen_top V) (le_preimage_top q ⊤)
  have : ((Scheme.Modules.pullback ρ₂).obj F).IsQuasicoherent :=
    Stacks.Modules.isQuasicoherent_pullback ρ₂ F inferInstance
  let modM : Module Γ(W, ⊤) Γ(F, ⊤) := baseModule (π ≫ q) F ⊤
  let modN : Module Γ(W, ⊤) Γ((Scheme.Modules.pullback ρ₂).obj F, ⊤) :=
    baseModule (ρ₂ ≫ π ≫ q) ((Scheme.Modules.pullback ρ₂).obj F) ⊤
  let modNA : Module Γ(V, ⊤) Γ((Scheme.Modules.pullback ρ₂).obj F, ⊤) :=
    baseModule k₁ ((Scheme.Modules.pullback ρ₂).obj F) ⊤
  let towN := baseTower sq₂ ((Scheme.Modules.pullback ρ₂).obj F) ⊤
  obtain ⟨e₂, he₂⟩ := exists_linearEquiv_sections_baseChange sq₂ F
  let modN₃ : Module Γ(W, ⊤)
      Γ((Scheme.Modules.pullback σ₂₃).obj ((Scheme.Modules.pullback ρ₂).obj F), ⊤) :=
    baseModule (σ₂₃ ≫ ρ₂ ≫ π ≫ q) _ ⊤
  let modN₃A : Module Γ(V, ⊤)
      Γ((Scheme.Modules.pullback σ₂₃).obj ((Scheme.Modules.pullback ρ₂).obj F), ⊤) :=
    baseModule k₃ _ ⊤
  let towN₃ := baseTower sq₃
    ((Scheme.Modules.pullback σ₂₃).obj ((Scheme.Modules.pullback ρ₂).obj F)) ⊤
  obtain ⟨e₃, he₃⟩ := exists_linearEquiv_sections_baseChange sq₃
    ((Scheme.Modules.pullback ρ₂).obj F)
  have hcomp : ∀ (p : X₂ ⟶ X) (a : Γ(W, ⊤)),
      (p.appLE ⊤ ⊤ (le_preimage_top p ⊤)).hom
          (((π ≫ q).appLE ⊤ ⊤ (le_preimage_top (π ≫ q) ⊤)).hom a) =
        ((p ≫ π ≫ q).appLE ⊤ ⊤ (le_preimage_top (p ≫ π ≫ q) ⊤)).hom a :=
    fun p ↦ appLE_top_appLE_top_of_comp_eq rfl
  have hW' : ∀ a : Γ(W, ⊤),
      ((ρ₁ ≫ π ≫ q).appLE ⊤ ⊤ (le_preimage_top (ρ₁ ≫ π ≫ q) ⊤)).hom a =
        ((ρ₂ ≫ π ≫ q).appLE ⊤ ⊤ (le_preimage_top (ρ₂ ≫ π ≫ q) ⊤)).hom a :=
    fun a ↦ congrArg (fun p : X₂ ⟶ W ↦ (p.appLE ⊤ ⊤ (le_preimage_top p ⊤)).hom a) hW
  let δ : Γ(F, ⊤) →ₗ[Γ(W, ⊤)] Γ((Scheme.Modules.pullback ρ₂).obj F, ⊤) :=
    { toFun := fun m ↦ κ.hom.app ⊤ (pullbackSectionsHom ρ₁ F ⊤ ⊤ (le_preimage_top ρ₁ ⊤) m) -
        pullbackSectionsHom ρ₂ F ⊤ ⊤ (le_preimage_top ρ₂ ⊤) m
      map_add' := fun m m' ↦ by
        simp only [map_add]
        abel
      map_smul' := fun a m ↦ by
        change κ.hom.app ⊤ (pullbackSectionsHom ρ₁ F ⊤ ⊤ (le_preimage_top ρ₁ ⊤)
            (((π ≫ q).appLE ⊤ ⊤ (le_preimage_top (π ≫ q) ⊤)).hom a • m)) -
          pullbackSectionsHom ρ₂ F ⊤ ⊤ (le_preimage_top ρ₂ ⊤)
            (((π ≫ q).appLE ⊤ ⊤ (le_preimage_top (π ≫ q) ⊤)).hom a • m) =
          ((ρ₂ ≫ π ≫ q).appLE ⊤ ⊤ (le_preimage_top (ρ₂ ≫ π ≫ q) ⊤)).hom a •
            (κ.hom.app ⊤ (pullbackSectionsHom ρ₁ F ⊤ ⊤ (le_preimage_top ρ₁ ⊤) m) -
              pullbackSectionsHom ρ₂ F ⊤ ⊤ (le_preimage_top ρ₂ ⊤) m)
        rw [pullbackSectionsHom_top_smul, pullbackSectionsHom_top_smul, Scheme.Modules.Hom.app_smul,
          hcomp, hcomp, hW', smul_sub] }
  let A₁ := ((Scheme.Modules.pullbackComp σ₁₂ ρ₂).hom.app F).app ⊤
  let A₂ := ((Scheme.Modules.pullbackCongr h₁₂₂).hom.app F).app ⊤
  let A₃ := pullHomApp κ.hom σ₂₃ t₂ t₃ h₂₃₁ h₂₃₂
  let A₄ := ((Scheme.Modules.pullbackCongr h₂₃₂).inv.app F).app ⊤
  let A₅ := ((Scheme.Modules.pullbackComp σ₂₃ ρ₂).inv.app F).app ⊤
  let B₁ := ((Scheme.Modules.pullbackComp σ₁₃ ρ₂).hom.app F).app ⊤
  let B₂ := ((Scheme.Modules.pullbackCongr h₁₃₂).hom.app F).app ⊤
  let Ψ : Γ((Scheme.Modules.pullback ρ₂).obj F, ⊤) →+
      Γ((Scheme.Modules.pullback σ₂₃).obj ((Scheme.Modules.pullback ρ₂).obj F), ⊤) :=
    A₅.hom.comp (A₄.hom.comp (A₃.hom.comp (A₂.hom.comp (A₁.hom.comp
      (pullbackSectionsHom σ₁₂ _ ⊤ ⊤ (le_preimage_top σ₁₂ ⊤)))))) -
    A₅.hom.comp (A₄.hom.comp (B₂.hom.comp (B₁.hom.comp
      (pullbackSectionsHom σ₁₃ _ ⊤ ⊤ (le_preimage_top σ₁₃ ⊤)))))
  have hΨ : ∀ y : Γ((Scheme.Modules.pullback ρ₂).obj F, ⊤), Ψ y =
      A₅ (A₄ (A₃ (A₂ (A₁ (pullbackSectionsHom σ₁₂ _ ⊤ ⊤ (le_preimage_top σ₁₂ ⊤) y))))) -
        A₅ (A₄ (B₂ (B₁ (pullbackSectionsHom σ₁₃ _ ⊤ ⊤ (le_preimage_top σ₁₃ ⊤) y)))) :=
    fun _ ↦ rfl
  have hinvhom : ∀ (x : Γ((Scheme.Modules.pullback σ₂₃).obj
      ((Scheme.Modules.pullback ρ₂).obj F), ⊤)),
      A₅ (((Scheme.Modules.pullbackComp σ₂₃ ρ₂).hom.app F).app ⊤ x) = x :=
    Scheme.Modules.app_top_inv_hom ((Scheme.Modules.pullbackComp σ₂₃ ρ₂).app F)
  have hcinvhom : ∀ (x : Γ((Scheme.Modules.pullback (σ₂₃ ≫ ρ₂)).obj F, ⊤)),
      A₄ (((Scheme.Modules.pullbackCongr h₂₃₂).hom.app F).app ⊤ x) = x :=
    Scheme.Modules.app_top_inv_hom ((Scheme.Modules.pullbackCongr h₂₃₂).app F)
  have hΦ₁ : ∀ m' : Γ(F, ⊤),
      A₅ (A₄ (A₃ (A₂ (A₁ (pullbackSectionsHom σ₁₂ _ ⊤ ⊤ (le_preimage_top σ₁₂ ⊤)
        (pullbackSectionsHom ρ₂ F ⊤ ⊤ (le_preimage_top ρ₂ ⊤) m')))))) =
      pullbackSectionsHom σ₂₃ _ ⊤ ⊤ (le_preimage_top σ₂₃ ⊤)
        (κ.hom.app ⊤ (pullbackSectionsHom ρ₁ F ⊤ ⊤ (le_preimage_top ρ₁ ⊤) m')) := fun m' ↦ by
    simp only [A₁, A₂, A₃]
    rw [pullbackComp_hom_app_pullbackSectionsHom, pullbackCongr_hom_app_pullbackSectionsHom,
      pullHomApp_pullbackSectionsHom, hcinvhom, hinvhom]
  have hΦ₂ : ∀ m' : Γ(F, ⊤),
      A₅ (A₄ (B₂ (B₁ (pullbackSectionsHom σ₁₃ _ ⊤ ⊤ (le_preimage_top σ₁₃ ⊤)
        (pullbackSectionsHom ρ₂ F ⊤ ⊤ (le_preimage_top ρ₂ ⊤) m'))))) =
      pullbackSectionsHom σ₂₃ _ ⊤ ⊤ (le_preimage_top σ₂₃ ⊤)
        (pullbackSectionsHom ρ₂ F ⊤ ⊤ (le_preimage_top ρ₂ ⊤) m') := fun m' ↦ by
    simp only [A₄, A₅, B₁, B₂]
    rw [pullbackComp_hom_app_pullbackSectionsHom, pullbackCongr_hom_app_pullbackSectionsHom,
      pullbackCongr_inv_app_pullbackSectionsHom, pullbackComp_inv_app_pullbackSectionsHom]
  have hk : ∀ (σ : X₃ ⟶ X₂), σ ≫ k₁ = k₃ → ∀ a : Γ(V, ⊤),
      (σ.appLE ⊤ ⊤ (le_preimage_top σ ⊤)).hom
          ((k₁.appLE ⊤ ⊤ (le_preimage_top k₁ ⊤)).hom a) =
        (k₃.appLE ⊤ ⊤ (le_preimage_top k₃ ⊤)).hom a := fun _ hσ ↦
    appLE_top_appLE_top_of_comp_eq hσ
  have hsmul₃ : ∀ (a : Γ(V, ⊤))
      (y : Γ((Scheme.Modules.pullback σ₂₃).obj ((Scheme.Modules.pullback ρ₂).obj F), ⊤)),
      a • y = (k₃.appLE ⊤ ⊤ (le_preimage_top k₃ ⊤)).hom a • y := fun _ _ ↦ rfl
  have hsmul₂ : ∀ (a : Γ(V, ⊤)) (y : Γ((Scheme.Modules.pullback ρ₂).obj F, ⊤)),
      a • y = (k₁.appLE ⊤ ⊤ (le_preimage_top k₁ ⊤)).hom a • y := fun _ _ ↦ rfl
  have hδ : ∀ m' : Γ(F, ⊤), δ m' =
      κ.hom.app ⊤ (pullbackSectionsHom ρ₁ F ⊤ ⊤ (le_preimage_top ρ₁ ⊤) m') -
        pullbackSectionsHom ρ₂ F ⊤ ⊤ (le_preimage_top ρ₂ ⊤) m' := fun _ ↦ rfl
  have hkey : ∀ z, e₃ (δ.lTensor Γ(V, ⊤) z) = Ψ (e₂ z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a m' =>
      rw [LinearMap.lTensor_tmul, he₃, he₂, hsmul₃, hsmul₂, hδ, hΨ,
        pullbackSectionsHom_top_smul, pullbackSectionsHom_top_smul]
      simp only [A₁, A₂, A₃, A₄, A₅, B₁, B₂, Scheme.Modules.Hom.app_smul]
      rw [pullHomApp_smul, Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul, hΦ₁, hΦ₂,
        hk σ₁₂ hk₁₂, hk σ₁₃ hk₁₃, map_sub, smul_sub]
    | add z₁ z₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂, map_add, map_add]
  have hP₁₂ : ((Scheme.Modules.pullbackCongr h₁₂₂).hom.app F).app ⊤
      (((Scheme.Modules.pullbackComp σ₁₂ ρ₂).hom.app F).app ⊤
        (pullbackSectionsHom σ₁₂ _ ⊤ ⊤ (le_preimage_top σ₁₂ ⊤)
          (κ.hom.app ⊤ (pullbackSectionsHom ρ₁ F ⊤ ⊤ (le_preimage_top ρ₁ ⊤) m)))) =
      pullHomApp κ.hom σ₁₂ t₁ t₂ h₁₂₁ h₁₂₂
        (pullbackSectionsHom t₁ F ⊤ ⊤ (le_preimage_top t₁ ⊤) m) :=
    (pullHomApp_pullbackSectionsHom κ.hom σ₁₂ t₁ t₂ h₁₂₁ h₁₂₂ m).symm
  have hcoc' := pullHomApp_comp κ.hom σ₁₂ σ₂₃ σ₁₃ t₁ t₂ t₃ h₁₂₁ h₁₂₂ h₂₃₁ h₂₃₂
    h₁₃₁ h₁₃₂ hcoc (pullbackSectionsHom t₁ F ⊤ ⊤ (le_preimage_top t₁ ⊤) m)
  have hP₁₃ := pullHomApp_pullbackSectionsHom κ.hom σ₁₃ t₁ t₃ h₁₃₁ h₁₃₂ m
  have hΨt : Ψ (κ.hom.app ⊤ (pullbackSectionsHom ρ₁ F ⊤ ⊤ (le_preimage_top ρ₁ ⊤) m)) = 0 := by
    rw [hΨ, sub_eq_zero]
    simp only [A₁, A₂, A₃, B₁, B₂]
    rw [hP₁₂, hcoc', hP₁₃]
  have hzero : δ.lTensor Γ(V, ⊤) (e₂.symm
      (κ.hom.app ⊤ (pullbackSectionsHom ρ₁ F ⊤ ⊤ (le_preimage_top ρ₁ ⊤) m))) = 0 := by
    apply e₃.injective
    rw [map_zero, hkey, LinearEquiv.apply_symm_apply, hΨt]
  obtain ⟨z, hz₀⟩ :=
    (Module.Flat.lTensor_exact Γ(V, ⊤) (LinearMap.exact_subtype_ker_map δ) _).mp hzero
  have hz : e₂ ((LinearMap.ker δ).subtype.lTensor Γ(V, ⊤) z) =
      κ.hom.app ⊤ (pullbackSectionsHom ρ₁ F ⊤ ⊤ (le_preimage_top ρ₁ ⊤) m) := by
    rw [hz₀, LinearEquiv.apply_symm_apply]
  have hx₁ : ρ₁.base (Δ.base x) = x := by
    simpa using congrArg (fun f : X ⟶ X ↦ f.base x) hΔ₁
  have hx₂ : ρ₂.base (Δ.base x) = x := by
    simpa using congrArg (fun f : X ⟶ X ↦ f.base x) hΔ₂
  have htx : Δ.base x ∈ nonvanishingLocus _
      (e₂ ((LinearMap.ker δ).subtype.lTensor Γ(V, ⊤) z)) := by
    rwa [hz, Stacks.Ample.nonvanishingLocus_congr κ, mem_nonvanishingLocus_pullbackSectionsHom_iff,
      hx₁]
  obtain ⟨m₀, hm₀, hxm₀⟩ := exists_mem_nonvanishingLocus_of_lTensor ρ₂ F (LinearMap.ker δ)
    e₂.toAddMonoidHom (fun a ↦ (k₁.appLE ⊤ ⊤ (le_preimage_top k₁ ⊤)).hom a)
    (fun a m' ↦ (he₂ a m').trans (hsmul₂ _ _)) z (Δ.base x) htx
  rw [hx₂] at hxm₀
  exact ⟨m₀, hxm₀, sub_eq_zero.mp (LinearMap.mem_ker.mp hm₀)⟩

end Stacks.Descent.InvariantSections
