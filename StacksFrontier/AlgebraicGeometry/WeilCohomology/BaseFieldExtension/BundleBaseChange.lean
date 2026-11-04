module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.BaseFieldExtension.Functor
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.ModuleFacts

/-!
# Base change of projective bundles of smooth projective schemes

For `X` smooth projective over `k` and `ℰ` finite locally free of rank `r + 1` on `X`, the
projective bundle of `ℰ_{k'}` on `X_{k'}` is the base change of `𝐏(ℰ)`, over `X_{k'}`, and the
twist `𝒪(1)` pulls back to the twist.

## Main definitions

* `baseChangeModule`: The pullback `ℰ_{k'}` of `ℰ` to `X_{k'}`.
* `bundleBaseChangeHom`: The base-change morphism `𝐏(ℰ_{k'}) ⟶ 𝐏(ℰ)`.
* `bundleBaseChangeIso`: The isomorphism `𝐏(ℰ_{k'}) ≅ 𝐏(ℰ)_{k'}` of smooth projective schemes
  over `k'`.
* `bundleBaseChangeTwistIso`: The pullback of `𝒪_{𝐏(ℰ)}(1)` to `𝐏(ℰ_{k'})` is
  `𝒪_{𝐏(ℰ_{k'})}(1)`.

## Main results

* `isPullback_bundleBaseChangeHom`: `𝐏(ℰ_{k'})` is the base change of `𝐏(ℰ)` along
  `Spec k' ⟶ Spec k`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.WeilCohomology.SmoothProjectiveScheme

variable {k : Type u} [Field k] {k' : Type u} [Field k'] [Algebra k k']
  (X : (SmoothProjectiveScheme k).FullSubcategory) (E : ((toScheme k).obj X).Modules) (r : ℕ)
  [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1)]

/-- The pullback `ℰ_{k'}` of `ℰ` to `X_{k'}`. -/
abbrev baseChangeModule : ((toScheme k').obj ((baseChange k k').obj X)).Modules :=
  (Scheme.Modules.pullback (baseChangeProj X)).obj E

/-- The pullback `ℰ_{k'}` is finite locally free of rank `r + 1`. -/
instance : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
    (baseChangeModule (k' := k') X E) (r + 1) :=
  Stacks.Chow.GenuineChern.isFiniteLocallyFreeOfRank_pullback _ E (r + 1)

/-- The base-change morphism `𝐏(ℰ_{k'}) ⟶ 𝐏(ℰ)` of schemes. -/
def bundleBaseChangeHom :
    (toScheme k').obj (bundle ((baseChange k k').obj X) (baseChangeModule (k' := k') X E) r) ⟶
      (toScheme k).obj (bundle X E r) :=
  letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E (r + 1)
  letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
    (baseChangeModule (k' := k') X E) (r + 1)
  Stacks.Chow.bundleBaseChangeHom (baseChangeProj X) E (baseChangeModule X E) (Iso.refl _)

/-- `𝐏(ℰ_{k'})` is the base change of `𝐏(ℰ)` along `Spec k' ⟶ Spec k`. -/
theorem isPullback_bundleBaseChangeHom :
    IsPullback (bundleBaseChangeHom (k' := k') X E r)
      (bundle ((baseChange k k').obj X) (baseChangeModule (k' := k') X E) r).obj.hom
      (bundle X E r).obj.hom (ArtinSchreier.specExt k k') := by
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E (r + 1)
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
    (baseChangeModule (k' := k') X E) (r + 1)
  exact (Stacks.Chow.isPullback_bundleBaseChangeHom (baseChangeProj X) E (baseChangeModule X E)
    (Iso.refl _)).flip.paste_vert (isPullback_baseChangeProj X)

/-- **`𝐏(ℰ_{k'}) ≅ 𝐏(ℰ)_{k'}`** as smooth projective schemes over `k'`. -/
def bundleBaseChangeIso :
    bundle ((baseChange k k').obj X) (baseChangeModule (k' := k') X E) r ≅
      (baseChange k k').obj (bundle X E r) where
  hom := homMk (isPullback_bundleBaseChangeHom X E r).isoPullback.hom
    (IsPullback.isoPullback_hom_snd _)
  inv := homMk (isPullback_bundleBaseChangeHom X E r).isoPullback.inv
    (IsPullback.isoPullback_inv_snd _)
  hom_inv_id := hom_ext' (by
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id]
    exact (isPullback_bundleBaseChangeHom X E r).isoPullback.hom_inv_id)
  inv_hom_id := hom_ext' (by
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id]
    exact (isPullback_bundleBaseChangeHom X E r).isoPullback.inv_hom_id)

/-- The isomorphism followed by the projection to `𝐏(ℰ)` is the base-change morphism. -/
@[reassoc]
theorem bundleBaseChangeIso_hom_proj :
    (toScheme k').map (bundleBaseChangeIso (k' := k') X E r).hom ≫
        baseChangeProj (bundle X E r) = bundleBaseChangeHom X E r :=
  IsPullback.isoPullback_hom_fst _

/-- The isomorphism lies over `X_{k'}`. -/
theorem bundleBaseChangeIso_hom_bundleProj :
    (bundleBaseChangeIso (k' := k') X E r).hom ≫ (baseChange k k').map (bundleProj X E r) =
      bundleProj ((baseChange k k').obj X) (baseChangeModule (k' := k') X E) r := by
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E (r + 1)
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
    (baseChangeModule (k' := k') X E) (r + 1)
  apply hom_ext'
  rw [Functor.map_comp]
  apply (isPullback_baseChangeProj X).hom_ext
  · rw [Category.assoc, baseChangeProj_naturality, ← Category.assoc, bundleBaseChangeIso_hom_proj]
    exact Stacks.Chow.bundleBaseChangeHom_bundleProj _ _ _ _
  · rw [Category.assoc, w, w]
    exact (w _).symm

/-- **The twist pulls back to the twist**: `𝒪_{𝐏(ℰ)}(1)` pulled back to `𝐏(ℰ)_{k'}` and then
along `𝐏(ℰ_{k'}) ≅ 𝐏(ℰ)_{k'}` is `𝒪_{𝐏(ℰ_{k'})}(1)`. -/
def bundleBaseChangeTwistIso :
    letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E (r + 1)
    letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
      (baseChangeModule (k' := k') X E) (r + 1)
    (Scheme.Modules.pullback ((toScheme k').map (bundleBaseChangeIso (k' := k') X E r).hom)).obj
        ((Scheme.Modules.pullback (baseChangeProj (bundle X E r))).obj
          (Stacks.Chow.bundleTwist E)) ≅
      Stacks.Chow.bundleTwist (baseChangeModule (k' := k') X E) :=
  letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E (r + 1)
  letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
    (baseChangeModule (k' := k') X E) (r + 1)
  (Scheme.Modules.pullbackComp ((toScheme k').map (bundleBaseChangeIso (k' := k') X E r).hom)
      (baseChangeProj (bundle X E r))).app _ ≪≫
    (Scheme.Modules.pullbackCongr ((bundleBaseChangeIso_hom_proj X E r).trans
      (Stacks.Chow.bundleBaseChangeIso_hom_snd (baseChangeProj X) E (baseChangeModule X E)
        (Iso.refl _)).symm)).app _ ≪≫
      (Stacks.Chow.bundleBaseChange (baseChangeProj X) E (baseChangeModule X E)
        (Iso.refl _)).twistIso

end Stacks.WeilCohomology.SmoothProjectiveScheme
