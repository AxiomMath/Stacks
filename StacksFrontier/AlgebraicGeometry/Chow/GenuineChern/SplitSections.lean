module

public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.SymSectionsHom
public import StacksFrontier.AlgebraicGeometry.Modules.LocallySplitShortExact
public import StacksFrontier.AlgebraicGeometry.InvertibleTrivialization.Basic
public import StacksFrontier.AlgebraicGeometry.NormInvertible.Generators

/-!
# An extension of a finite locally free module by an invertible one, on sections

Let `0 ⟶ ℳ ⟶ 𝒢 ⟶ 𝒬 ⟶ 0` be a short exact sequence of modules on a scheme `X` with `ℳ`
invertible and `𝒬` finite locally free. Every point of `X` has an affine open neighbourhood `O`
over which `ℳ` is trivialized by a section `m₀` and the sequence of sections
`0 ⟶ Γ(X, O) ⟶ Γ(𝒢, O) ⟶ Γ(𝒬, O) ⟶ 0`, `1 ↦ m₀`, is exact and split. These are the hypotheses
of `Stacks.SymGraded.AffinePieces.ker_sectionHom_eq_span_of_split`.

The sequence splits over a neighbourhood of every point
(`AlgebraicGeometry.Scheme.Modules.exists_nonempty_splitting_restrict_of_isFiniteLocallyFree`),
`ℳ` is trivialized over a neighbourhood of every point
(`Stacks.SheafOfModules.exists_bijective_smul_of_isInvertible`), and `O` is an affine open inside
both. The open is chosen as the image of an affine open of the splitting neighbourhood, so that
the sections of the restricted modules are the sections over `O` on the nose.

## Main results

* `Stacks.Chow.GenuineChern.exists_affine_split_sections`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Stacks.SymGraded.AffinePieces

universe u

namespace Stacks.Chow.GenuineChern

variable {X : Scheme.{u}}

/-- The sections over the image of an open of `U` of a morphism of modules restricted to `U`
are the sections of the morphism. -/
theorem restrictFunctor_map_app {U : X.Opens} {M N : X.Modules} (φ : M ⟶ N) (W : U.toScheme.Opens)
    (x : Γ(M, U.ι ''ᵁ W)) :
    ((Scheme.Modules.restrictFunctor U.ι).map φ).app W x = φ.app (U.ι ''ᵁ W) x := rfl

/-- The action of a function on `U` on the sections of a restricted module is the action of the
corresponding function on `X`. -/
theorem restrict_smul_eq {U : X.Opens} (M : X.Modules) (W : U.toScheme.Opens) (c : Γ(X, U.ι ''ᵁ W))
    (x : Γ(M.restrict U.ι, W)) :
    @id Γ(M, U.ι ''ᵁ W) (((U.ι.appIso W).hom c) • x) = c • @id Γ(M, U.ι ''ᵁ W) x := by
  have h := Scheme.Modules.smul_restrictAppIso_hom_apply U.ι M W ((U.ι.appIso W).hom c) x
  rwa [Iso.hom_inv_id_apply] at h

/-- A morphism of restricted modules is linear over the sections of `X` on the sections over the
image of an open, which are the sections of the restricted modules. -/
theorem restrict_hom_app_smul {U : X.Opens} {M N : X.Modules}
    (φ : M.restrict U.ι ⟶ N.restrict U.ι) (W : U.toScheme.Opens) (c : Γ(X, U.ι ''ᵁ W))
    (x : Γ(M, U.ι ''ᵁ W)) :
    @id Γ(N, U.ι ''ᵁ W) (φ.app W (c • x)) = c • @id Γ(N, U.ι ''ᵁ W) (φ.app W x) := by
  rw [← restrict_smul_eq N W c (φ.app W x)]
  have h := restrict_smul_eq M W c x
  simp only [id] at h ⊢
  rw [← h]
  exact Scheme.Modules.Hom.app_smul φ _ x

/-- A morphism of restricted modules on the sections over the image of an open, as a linear map
over the sections of `X`. -/
def restrictSectionsLinearMap {U : X.Opens} {M N : X.Modules}
    (φ : M.restrict U.ι ⟶ N.restrict U.ι) (W : U.toScheme.Opens) :
    Γ(M, U.ι ''ᵁ W) →ₗ[Γ(X, U.ι ''ᵁ W)] Γ(N, U.ι ''ᵁ W) where
  toFun x := (φ.app W).hom x
  map_add' x y := map_add (φ.app W).hom x y
  map_smul' c x := restrict_hom_app_smul φ W c x

/-- The linear map `restrictSectionsLinearMap φ W` sends a section `x` to `φ.app W x`. -/
theorem restrictSectionsLinearMap_apply {U : X.Opens} {M N : X.Modules}
    (φ : M.restrict U.ι ⟶ N.restrict U.ι) (W : U.toScheme.Opens) (x : Γ(M, U.ι ''ᵁ W)) :
    restrictSectionsLinearMap φ W x = φ.app W x := rfl

/-- Bijectivity of multiplication by a section, transported along an equality of sections; the
conclusion is checked against the expected type, which crosses the spellings of the structure
sheaf (as `Stacks.SheafOfModules.bijective_smul_congr` does). -/
theorem bijective_smul_congr' (L : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    {W : X.Opens} {a b : L.val.obj (op W)} (hab : a = b)
    (hb : Function.Bijective fun c : X.presheaf.obj (op W) => c • b) :
    Function.Bijective fun c : X.presheaf.obj (op W) => c • a := hab ▸ hb

/-- **A split extension by a free module of rank one, on sections.** If the restriction of `S` to
an open `U` splits and `m` generates `Γ(𝒮.X₁, O)` freely over the image `O` of an open of `U`,
then `Γ(𝒮.X₂, O) ⟶ Γ(𝒮.X₃, O)` is surjective with kernel spanned by the image of `m`, and a
linear functional takes the value `1` on that image. -/
theorem split_sections_of_splitting (S : ShortComplex X.Modules) {U : X.Opens}
    (sp : (S.map (Scheme.Modules.restrictFunctor U.ι)).Splitting) (W' : U.toScheme.Opens)
    (m : Γ(S.X₁, U.ι ''ᵁ W'))
    (hm : Function.Bijective (LinearMap.toSpanSingleton Γ(X, U.ι ''ᵁ W') Γ(S.X₁, U.ι ''ᵁ W') m)) :
    Function.Surjective (sectionsLinearMap S.g (U.ι ''ᵁ W')) ∧
      LinearMap.ker (sectionsLinearMap S.g (U.ι ''ᵁ W')) =
        Submodule.span Γ(X, U.ι ''ᵁ W') {S.f.app _ m} ∧
      ∃ l : Γ(S.X₂, U.ι ''ᵁ W') →ₗ[Γ(X, U.ι ''ᵁ W')] Γ(X, U.ι ''ᵁ W'), l (S.f.app _ m) = 1 := by
  set ρ := restrictSectionsLinearMap sp.r W'
  set σ := restrictSectionsLinearMap sp.s W'
  have key : ∀ {A B : U.toScheme.Modules} {φ ψ : A ⟶ B}, φ = ψ →
      ∀ x : Γ(A, W'), (φ.app W').hom x = (ψ.app W').hom x := fun h _ => by rw [h]
  have fr : ∀ n : Γ(S.X₁, U.ι ''ᵁ W'), ρ (S.f.app _ n) = n := fun n => key sp.f_r n
  have sg : ∀ q : Γ(S.X₃, U.ι ''ᵁ W'), S.g.app _ (σ q) = q := fun q => key sp.s_g q
  have idx : ∀ y : Γ(S.X₂, U.ι ''ᵁ W'), S.f.app _ (ρ y) + σ (S.g.app _ y) = y := fun y =>
    key sp.id y
  have hzero : ∀ n : Γ(S.X₁, U.ι ''ᵁ W'), S.g.app _ (S.f.app _ n) = 0 := fun n =>
    congrArg (fun φ : S.X₁ ⟶ S.X₃ => (φ.app (U.ι ''ᵁ W')).hom n) S.zero
  set e := LinearEquiv.ofBijective _ hm
  refine ⟨fun q => ⟨σ q, sg q⟩, ?_, ⟨e.symm ∘ₗ ρ, ?_⟩⟩
  · ext y
    rw [LinearMap.mem_ker, Submodule.mem_span_singleton]
    refine ⟨fun hy => ?_, ?_⟩
    · obtain ⟨c, hc⟩ := hm.2 (ρ y)
      refine ⟨c, ?_⟩
      have hy' := idx y
      change S.g.app _ y = 0 at hy
      rw [hy, map_zero, add_zero] at hy'
      rw [← hy', ← hc]
      exact (Scheme.Modules.Hom.app_smul S.f c m).symm
    · rintro ⟨c, rfl⟩
      show S.g.app _ (c • S.f.app _ m) = 0
      rw [Scheme.Modules.Hom.app_smul, hzero, smul_zero]
  · show e.symm (ρ (S.f.app _ m)) = 1
    rw [fr, LinearEquiv.symm_apply_eq]
    exact (one_smul _ m).symm

/-- **An extension of a finite locally free module by an invertible one is, over a small affine
open, a split extension of the sections by a free module of rank one.** Every point of `X` has an
affine open neighbourhood `O` and a generator `m₀` of `ℳ` over `O` (multiplication by its
restriction is bijective on every open `W ≤ O`) such that `Γ(𝒢, O) ⟶ Γ(𝒬, O)` is surjective with
kernel spanned by the image of `m₀`, and a linear functional on `Γ(𝒢, O)` takes the value `1` on
that image. -/
theorem exists_affine_split_sections (S : ShortComplex X.Modules) (hS : S.ShortExact)
    [hM : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property S.X₁]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} S.X₃] (x : X) :
    ∃ (O : X.Opens) (_ : IsAffineOpen O) (_ : x ∈ O)
      (m₀ : Stacks.SheafOfModules.GeneratorSections X.toRingedSpace S.X₁ O),
      Function.Surjective (sectionsLinearMap S.g O) ∧
      LinearMap.ker (sectionsLinearMap S.g O) =
        Submodule.span Γ(X, O) {S.f.app O m₀.val} ∧
      ∃ l : Γ(S.X₂, O) →ₗ[Γ(X, O)] Γ(X, O), l (S.f.app O m₀.val) = 1 := by
  have hlocal : ∀ z : X.toRingedSpace.carrier,
      IsLocalRing (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk X.toRingedSpace z) :=
    X.isLocalRing
  have : Stacks.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property S.X₁ :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).2 hM
  obtain ⟨T, hxT, a, ha⟩ :=
    Stacks.SheafOfModules.exists_bijective_smul_of_isInvertible (X := X.toRingedSpace) S.X₁ x
  let gT : Stacks.SheafOfModules.GeneratorSections X.toRingedSpace S.X₁ T :=
    ⟨a, fun V h => bijective_smul_congr' S.X₁
      (PresheafOfModules.restrictₛₗ_apply _ _ _) (ha V h)⟩
  obtain ⟨U, hxU, ⟨sp⟩⟩ :=
    Scheme.Modules.exists_nonempty_splitting_restrict_of_isFiniteLocallyFree S hS x
  have hxT' : (⟨x, hxU⟩ : U.toScheme) ∈ U.ι ⁻¹ᵁ T := hxT
  obtain ⟨W', hW', hxW', hW'T⟩ := exists_isAffineOpen_mem_and_subset hxT'
  have hOT : U.ι ''ᵁ W' ≤ T := by
    rintro _ ⟨y, hy, rfl⟩
    exact hW'T hy
  let m₀ := Stacks.SheafOfModules.generatorRestrict S.X₁ hOT gT
  exact ⟨U.ι ''ᵁ W', hW'.image_of_isOpenImmersion U.ι, ⟨⟨x, hxU⟩, hxW', rfl⟩, m₀,
    split_sections_of_splitting S sp W' m₀.val (bijective_smul_congr' S.X₁
      (Stacks.SheafOfModules.generator_restrict_self (X := X.toRingedSpace) S.X₁ _ m₀).symm
      (m₀.property _ (le_refl _)))⟩

end Stacks.Chow.GenuineChern

end
