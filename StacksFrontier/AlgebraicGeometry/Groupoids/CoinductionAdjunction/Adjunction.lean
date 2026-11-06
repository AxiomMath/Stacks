module

public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.AffineBaseReduction
public import StacksFrontier.AlgebraicGeometry.GroupScheme.QuasicoherentPullbackFunctor
public import StacksFrontier.AlgebraicGeometry.Groupoids.Coinduction
public import StacksFrontier.AlgebraicGeometry.Groupoids.Equivariant.PushforwardDescent
public import StacksFrontier.AlgebraicGeometry.Groupoids.QuasicoherentFromBase
public import StacksFrontier.AlgebraicGeometry.Simplicial.GroupoidQuasiCoherentComparison
public import StacksFrontier.AlgebraicGeometry.Groupoids.CoinductionAdjunction.CocycleCondition
public import StacksFrontier.AlgebraicGeometry.Groupoids.CoinductionAdjunction.IdentityRestriction

/-!
# Coinduction is right adjoint to forgetting a groupoid descent datum

Let `(U, R, s, t, c)` be a groupoid scheme with `s` and `t` flat and `s` quasi-compact and
quasi-separated.  Using the cocycle condition and the normalization of the descent morphism `α` of
`s_* t^* 𝒢`, this file shows that `(s_* t^* 𝒢, α)` is a quasi-coherent module on the groupoid
scheme, and that the resulting functor is right adjoint to the forgetful functor.  The unit of
that adjunction is computed: at `(ℱ, α)` it is the unit of the pullback--pushforward adjunction
along `s` followed by the direct image of `α⁻¹`.

## Main definitions

* `Stacks.Groupoids.GroupoidScheme.quasicoherentForget` is the forgetful functor to the category
  of quasi-coherent modules on the scheme of objects.
* `Stacks.Groupoids.GroupoidScheme.coinduction` is the functor `𝒢 ↦ (s_* t^* 𝒢, α)`.
* `Stacks.Groupoids.GroupoidScheme.coinductionAdjunction` is the adjunction between them.

## Main results

* `Stacks.Groupoids.GroupoidScheme.coinductionAdjunction_unit_app`: the unit of the adjunction,
  on underlying modules, is `ℱ ⟶ s_* s^* ℱ ⟶ s_* t^* ℱ`, the second map being the direct image
  of the inverse of the descent morphism.

## Implementation notes

The underlying module of `coinduction` is *by definition* `s_* t^* 𝒢`, not merely isomorphic to
it, so the unit formula is an equality of morphisms of modules on the scheme of objects and needs
no comparison isomorphism.

## References

* [Stacks Project, Tag 07TR](https://stacks.math.columbia.edu/tag/07TR)
* [Stacks Project, Tag 0GNF](https://stacks.math.columbia.edu/tag/0GNF)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.AffinePushforward (baseChangeNatTrans)
open Stacks.AlgebraicGeometry.FlatBaseChangeCohomology (pasteBase
  baseChangeNatTrans_pasteBase_app isIso_baseChangeNatTrans_of_flat)

universe u

namespace Stacks.Groupoids.GroupoidScheme

/-! ### The equivariance condition on the scheme of composable arrows -/

section Coinduction

open GroupoidScheme

variable {S : Scheme.{u}} (G : GroupoidScheme S)
  [Flat G.source.left] [Flat G.target.left]
  [QuasiCompact G.source.left] [QuasiSeparated G.source.left]

/-- The inverse image of a morphism between two pullbacks, in terms of `reindexHom₂`. -/
theorem pullback_map_eq_reindexHom₂ {X Y Z : Scheme.{u}} (f : X ⟶ Y) {g h : Y ⟶ Z}
    {F F' : Z.Modules}
    (ψ : (Scheme.Modules.pullback g).obj F ⟶ (Scheme.Modules.pullback h).obj F') :
    (Scheme.Modules.pullback f).map ψ =
      (Scheme.Modules.pullbackComp f g).hom.app F ≫ reindexHom₂ f ψ ≫
        (Scheme.Modules.pullbackComp f h).inv.app F' := by
  simp [reindexHom₂]

/-- **Descent compatibility across the transpose.**  A morphism `u : s^* 𝓕 ⟶ t^* 𝒢` has a
transpose along `s` which intertwines the descent morphism of `𝓕` with the canonical descent
morphism of `s_* t^* 𝒢` exactly when `u` satisfies the displayed condition on the scheme of
composable arrows. -/
theorem comm_iff (M : QuasicoherentModule G) (𝒢 : G.objects.left.Modules)
    [𝒢.IsQuasicoherent]
    (u : (Scheme.Modules.pullback G.source.left).obj M.module ⟶
      (Scheme.Modules.pullback G.target.left).obj 𝒢) :
    (M.alpha ≫ (Scheme.Modules.pullback G.source.left).map
          ((Scheme.Modules.pullbackPushforwardAdjunction G.source.left).homEquiv M.module
            ((Scheme.Modules.pullback G.target.left).obj 𝒢) u) =
        (Scheme.Modules.pullback G.target.left).map
            ((Scheme.Modules.pullbackPushforwardAdjunction G.source.left).homEquiv M.module
              ((Scheme.Modules.pullback G.target.left).obj 𝒢) u) ≫
          (coinductionAlpha G 𝒢).hom) ↔
      ((Scheme.Modules.pullback (pullback.snd G.source G.target).left).map M.alpha ≫
          (Stacks.Modules.pullbackSquareIso G.source.left
              (pullback.snd G.source G.target).left G.source.left G.comp.left
              (isPullback_comp_snd_source G).w).hom.app M.module ≫
          (Scheme.Modules.pullback G.comp.left).map u =
        (Stacks.Modules.pullbackSquareIso G.source.left
              (pullback.snd G.source G.target).left G.target.left
              (pullback.fst G.source G.target).left
              (isPullback_composableArrows G).w).hom.app M.module ≫
          (Scheme.Modules.pullback (pullback.fst G.source G.target).left).map u ≫
          (coinductionComparison G).hom.app 𝒢) := by
  have hqc : ((Scheme.Modules.pullback G.target.left).obj 𝒢).IsQuasicoherent :=
    isQuasicoherent_pullbackTarget G 𝒢
  have hS : IsIso ((coinductionSourceBaseChange G).app
      ((Scheme.Modules.pullback G.target.left).obj 𝒢)) :=
    isIso_coinductionSourceBaseChange_app G _
  have hMono : Mono ((coinductionSourceBaseChange G).app
      ((Scheme.Modules.pullback G.target.left).obj 𝒢)) := IsIso.mono_of_iso _
  have hinv : (coinductionSourceBaseChangeIso G
        ((Scheme.Modules.pullback G.target.left).obj 𝒢)).inv ≫
      (coinductionSourceBaseChange G).app
        ((Scheme.Modules.pullback G.target.left).obj 𝒢) = 𝟙 _ :=
    (coinductionSourceBaseChangeIso G _).inv_hom_id
  have hA : (coinductionAlpha G 𝒢).hom ≫ (coinductionSourceBaseChange G).app
        ((Scheme.Modules.pullback G.target.left).obj 𝒢) =
      (coinductionTargetBaseChange G).app
          ((Scheme.Modules.pullback G.target.left).obj 𝒢) ≫
        (Scheme.Modules.pushforward (pullback.snd G.source G.target).left).map
          ((coinductionComparison G).hom.app 𝒢) := by
    simp [coinductionAlpha, hinv]
  have hT := Stacks.Groupoids.pullback_map_homEquiv_comp_baseChangeNatTrans
    (isPullback_composableArrows G).w u
  have hSq := Stacks.Groupoids.pullback_map_homEquiv_comp_baseChangeNatTrans
    (isPullback_comp_snd_source G).w u
  rw [← cancel_mono ((coinductionSourceBaseChange G).app
    ((Scheme.Modules.pullback G.target.left).obj 𝒢))]
  simp only [Category.assoc]
  rw [hA, coinductionSourceBaseChange, coinductionTargetBaseChange]
  rw [hSq, reassoc_of% hT, ← Adjunction.homEquiv_naturality_left,
    ← Adjunction.homEquiv_naturality_right]
  simp only [Functor.comp_obj]
  rw [Equiv.apply_eq_iff_eq]
  simp only [Category.assoc]

/-- **The equivariance condition, in reindexing form.**  The descent compatibility of the
transpose of `u`, written with the comparisons of the pullbacks along the composites rather
than with the comparisons around the two cartesian squares. -/
theorem reindex_comm (M : QuasicoherentModule G) (𝒢 : G.objects.left.Modules)
    [𝒢.IsQuasicoherent]
    (u : (Scheme.Modules.pullback G.source.left).obj M.module ⟶
      (Scheme.Modules.pullback G.target.left).obj 𝒢)
    (hu : M.alpha ≫ (Scheme.Modules.pullback G.source.left).map
          ((Scheme.Modules.pullbackPushforwardAdjunction G.source.left).homEquiv M.module
            ((Scheme.Modules.pullback G.target.left).obj 𝒢) u) =
        (Scheme.Modules.pullback G.target.left).map
            ((Scheme.Modules.pullbackPushforwardAdjunction G.source.left).homEquiv M.module
              ((Scheme.Modules.pullback G.target.left).obj 𝒢) u) ≫
          (coinductionAlpha G 𝒢).hom)
    (hS : (pullback.snd G.source G.target).left ≫ G.source.left =
      G.comp.left ≫ G.source.left)
    (hT : (pullback.snd G.source G.target).left ≫ G.target.left =
      (pullback.fst G.source G.target).left ≫ G.source.left)
    (hC : (pullback.fst G.source G.target).left ≫ G.target.left =
      G.comp.left ≫ G.target.left) :
    reindexHom (pullback.snd G.source G.target).left M.alpha ≫
        (Scheme.Modules.pullbackCongr hS).hom.app M.module ≫
        reindexHom₂ G.comp.left u =
      (Scheme.Modules.pullbackCongr hT).hom.app M.module ≫
        reindexHom₂ (pullback.fst G.source G.target).left u ≫
        (Scheme.Modules.pullbackCongr hC).hom.app 𝒢 := by
  have X := (comm_iff G M 𝒢 u).1 hu
  rw [pullback_map_eq_reindexHom₂, pullback_map_eq_reindexHom₂, pullback_map_eq_reindexHom₂,
    Stacks.Modules.pullbackSquareIso, Stacks.Modules.pullbackSquareIso,
    coinductionComparison] at X
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc,
    Iso.inv_hom_id_app_assoc, Stacks.Modules.pullbackCongr_hom_app] at X
  have hEpi : Epi ((Scheme.Modules.pullbackComp (pullback.snd G.source G.target).left
      G.target.left).hom.app M.module) := IsIso.epi_of_iso _
  have hMono : Mono ((Scheme.Modules.pullbackComp G.comp.left G.target.left).inv.app 𝒢) :=
    IsIso.mono_of_iso _
  rw [← cancel_epi ((Scheme.Modules.pullbackComp (pullback.snd G.source G.target).left
      G.target.left).hom.app M.module),
    ← cancel_mono ((Scheme.Modules.pullbackComp G.comp.left G.target.left).inv.app 𝒢),
    ← reindexHom₂_eq_reindexHom]
  simp only [Category.assoc, Stacks.Modules.pullbackCongr_hom_app]
  exact X

/-- **The key step of the inverse round trip.**  A morphism `u : s^*𝓕 ⟶ t^*𝒢` whose transpose
along the source is compatible with the descent morphisms is recovered from its restriction
along the identity section:  the descent morphism followed by `u` is the inverse image along the
target of that restriction.  Reindexing the equivariance condition along the section pairing the
identity arrow at the target of an arrow with the arrow itself is what forces this. -/
theorem alpha_comp_eq_pullback_map_identityRestrict (M : QuasicoherentModule G)
    (𝒢 : G.objects.left.Modules) [𝒢.IsQuasicoherent]
    (u : (Scheme.Modules.pullback G.source.left).obj M.module ⟶
      (Scheme.Modules.pullback G.target.left).obj 𝒢)
    (hu : M.alpha ≫ (Scheme.Modules.pullback G.source.left).map
          ((Scheme.Modules.pullbackPushforwardAdjunction G.source.left).homEquiv M.module
            ((Scheme.Modules.pullback G.target.left).obj 𝒢) u) =
        (Scheme.Modules.pullback G.target.left).map
            ((Scheme.Modules.pullbackPushforwardAdjunction G.source.left).homEquiv M.module
              ((Scheme.Modules.pullback G.target.left).obj 𝒢) u) ≫
          (coinductionAlpha G 𝒢).hom) :
    M.alpha ≫ u = (Scheme.Modules.pullback G.target.left).map (identityRestrict G u) := by
  have K := reindex_comm G M 𝒢 u hu (isPullback_comp_snd_source G).w.symm
    (isPullback_composableArrows G).w.symm (comp_left_comp_target_left G).symm
  have Kτ := congrArg (reindexHom₂ (targetIdentitySection G).left) K
  rw [reindexHom₂_comp, reindexHom₂_comp, reindexHom₂_comp, reindexHom₂_comp] at Kτ
  rw [reindexHom₂_eq_reindexHom, Stacks.Groupoids.reindexHom_assoc_rev,
    Stacks.Groupoids.reindexHom_congr_source (targetIdentitySection_snd_left G),
    Stacks.Groupoids.reindexHom_id_left, reindexHom₂_congr, reindexHom₂_assoc_rev',
    reindexHom₂_congr_source (targetIdentitySection_comp_left G), reindexHom₂_id_left',
    reindexHom₂_congr, reindexHom₂_assoc_rev',
    reindexHom₂_congr_source (targetIdentitySection_fst_left G), reindexHom₂_assoc',
    reindexHom₂_congr] at Kτ
  simp only [Stacks.Modules.pullbackCongr_hom_app, Category.assoc, eqToHom_trans,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] at Kτ
  rw [pullback_map_identityRestrict G u
    (by rw [identity_left_comp_source_left G, Category.comp_id])
    (by rw [identity_left_comp_target_left G, Category.comp_id])]
  have K1 := (eqToHom_comp_iff _ _ _).mp Kτ
  rw [← Category.assoc M.alpha u] at K1
  rw [(comp_eqToHom_iff _ _ _).mp K1]
  simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]

/-- **The second round trip.**  On a morphism `𝓕 ⟶ s_* t^* 𝒢` which intertwines the descent
morphism of `𝓕` with the canonical descent morphism of `s_* t^* 𝒢`, the forward map undoes the
inverse map.  With `untranspose_transpose` this exhibits the two maps as mutually inverse
bijections between `Hom(𝓕, 𝒢)` and the descent-compatible morphisms `𝓕 ⟶ s_* t^* 𝒢`. -/
theorem transpose_untranspose (M : QuasicoherentModule G) (𝒢 : G.objects.left.Modules)
    [𝒢.IsQuasicoherent]
    (g : M.module ⟶ (Scheme.Modules.pushforward G.source.left).obj
      ((Scheme.Modules.pullback G.target.left).obj 𝒢))
    (hg : M.alpha ≫ (Scheme.Modules.pullback G.source.left).map g =
      (Scheme.Modules.pullback G.target.left).map g ≫ (coinductionAlpha G 𝒢).hom) :
    transpose G M 𝒢 (untranspose G M 𝒢 g) = g := by
  have hu : M.alpha ≫ (Scheme.Modules.pullback G.source.left).map
        ((Scheme.Modules.pullbackPushforwardAdjunction G.source.left).homEquiv M.module
          ((Scheme.Modules.pullback G.target.left).obj 𝒢)
          (((Scheme.Modules.pullbackPushforwardAdjunction G.source.left).homEquiv M.module
            ((Scheme.Modules.pullback G.target.left).obj 𝒢)).symm g)) =
      (Scheme.Modules.pullback G.target.left).map
          ((Scheme.Modules.pullbackPushforwardAdjunction G.source.left).homEquiv M.module
            ((Scheme.Modules.pullback G.target.left).obj 𝒢)
            (((Scheme.Modules.pullbackPushforwardAdjunction G.source.left).homEquiv M.module
              ((Scheme.Modules.pullback G.target.left).obj 𝒢)).symm g)) ≫
        (coinductionAlpha G 𝒢).hom := by
    rw [Equiv.apply_symm_apply]
    exact hg
  have hkey := alpha_comp_eq_pullback_map_identityRestrict G M 𝒢 _ hu
  rw [untranspose, identityRestrictTarget_alpha_comp, transpose, ← hkey,
    IsIso.inv_hom_id_assoc, Equiv.apply_symm_apply]

end Coinduction


/-! ### The coinduction functor, the transpose, and the adjunction -/


/-- The inverse image of a morphism between two pullbacks, in terms of `reindexHom`. -/
theorem pullback_map_eq_reindexHom {X Y Z : Scheme.{u}} (f : X ⟶ Y) {g h : Y ⟶ Z}
    {F : Z.Modules}
    (α : (Scheme.Modules.pullback g).obj F ⟶ (Scheme.Modules.pullback h).obj F) :
    (Scheme.Modules.pullback f).map α =
      (Scheme.Modules.pullbackComp f g).hom.app F ≫ reindexHom f α ≫
        (Scheme.Modules.pullbackComp f h).inv.app F := by
  simp [reindexHom]

/-- Reindexing an invertible descent morphism and then its inverse is the identity. -/
@[simp, reassoc]
theorem reindexHom_comp_reindexHom_inv {X Y Z : Scheme.{u}} (f : X ⟶ Y) {g h : Y ⟶ Z}
    {F : Z.Modules}
    (α : (Scheme.Modules.pullback g).obj F ⟶ (Scheme.Modules.pullback h).obj F) [IsIso α] :
    reindexHom f α ≫ reindexHom f (inv α) = 𝟙 _ := by
  rw [← reindexHom_comp, IsIso.hom_inv_id, reindexHom_id]

/-- Reindexing the inverse of an invertible descent morphism and then the morphism is the
identity. -/
@[simp, reassoc]
theorem reindexHom_inv_comp_reindexHom {X Y Z : Scheme.{u}} (f : X ⟶ Y) {g h : Y ⟶ Z}
    {F : Z.Modules}
    (α : (Scheme.Modules.pullback g).obj F ⟶ (Scheme.Modules.pullback h).obj F) [IsIso α] :
    reindexHom f (inv α) ≫ reindexHom f α = 𝟙 _ := by
  rw [← reindexHom_comp, IsIso.inv_hom_id, reindexHom_id]

/-- The purely formal rearrangement of a five-factor cocycle identity used below. -/
theorem cocycle_rearrange {C : Type*} [Category C] {A B D E F F' : C}
    (p : A ⟶ B) (r₀ : B ⟶ D) (q : D ⟶ E) (r₁ : E ⟶ F) (w : F ⟶ F') (rc : A ⟶ F')
    (pi : B ⟶ A) (qi : E ⟶ D) (r₀' : D ⟶ B) (rc' : F' ⟶ A)
    (hcoc : p ≫ r₀ ≫ q ≫ r₁ ≫ w = rc)
    (hpi : pi ≫ p = 𝟙 B) (hqi : qi ≫ q = 𝟙 E) (hr₀ : r₀' ≫ r₀ = 𝟙 D)
    (hrc : rc ≫ rc' = 𝟙 A) :
    r₁ ≫ w ≫ rc' = qi ≫ r₀' ≫ pi := by
  calc r₁ ≫ w ≫ rc' = (qi ≫ q) ≫ r₁ ≫ w ≫ rc' := by rw [hqi, Category.id_comp]
    _ = qi ≫ (r₀' ≫ r₀) ≫ q ≫ r₁ ≫ w ≫ rc' := by simp [hr₀]
    _ = qi ≫ r₀' ≫ (pi ≫ p) ≫ r₀ ≫ q ≫ r₁ ≫ w ≫ rc' := by simp [hpi]
    _ = qi ≫ r₀' ≫ pi ≫ (p ≫ r₀ ≫ q ≫ r₁ ≫ w) ≫ rc' := by simp
    _ = qi ≫ r₀' ≫ pi ≫ rc ≫ rc' := by rw [hcoc]
    _ = qi ≫ r₀' ≫ pi := by simp [hrc]

/-- Pulling the inverse image of a morphism back once more, through the comparison of the
iterated inverse image with the inverse image along the composite. -/
theorem pullbackComp_naturality_map {V' W X : Scheme.{u}} (p : V' ⟶ W) (x : W ⟶ X)
    {A B : X.Modules} (ψ : A ⟶ B) :
    (Scheme.Modules.pullback p).map ((Scheme.Modules.pullback x).map ψ) =
      (Scheme.Modules.pullbackComp p x).hom.app A ≫
        (Scheme.Modules.pullback (p ≫ x)).map ψ ≫
        (Scheme.Modules.pullbackComp p x).inv.app B := by
  have h := (Scheme.Modules.pullbackComp p x).hom.naturality ψ
  simp only [Functor.comp_map] at h
  rw [← Category.assoc, ← h]
  simp

/-- Pulling the canonical comparison back once more gives the canonical comparison of the
composites, conjugated by the comparisons of the iterated inverse images. -/
theorem pullback_map_baseComparison {V' W V X : Scheme.{u}} (p : V' ⟶ W) {a b : W ⟶ V}
    (φ : V ⟶ X) (h : a ≫ φ = b ≫ φ) (F : X.Modules) :
    (Scheme.Modules.pullback p).map (baseComparison φ h F) =
      (Scheme.Modules.pullbackComp p a).hom.app ((Scheme.Modules.pullback φ).obj F) ≫
        baseComparison φ (by rw [Category.assoc, Category.assoc, h] :
          (p ≫ a) ≫ φ = (p ≫ b) ≫ φ) F ≫
        (Scheme.Modules.pullbackComp p b).inv.app ((Scheme.Modules.pullback φ).obj F) := by
  rw [pullback_map_eq_reindexHom, reindexHom_baseComparison]

/-! ### Pullback along a section -/

section Section

variable {V U : Scheme.{u}} (q : V ⟶ U)

/-- The right unitality of the pullback pseudofunctor, in componentwise form. -/
theorem pullbackComp_id_left_app (Y : U.Modules) :
    (Scheme.Modules.pullbackComp (𝟙 V) q).inv.app Y ≫
        (Scheme.Modules.pullbackId V).hom.app ((Scheme.Modules.pullback q).obj Y) =
      (Scheme.Modules.pullbackCongr (Category.id_comp q)).hom.app Y := by
  have pg := NatTrans.congr_app (Scheme.Modules.pseudofunctor_right_unitality q) Y
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app] at pg
  simp only [Functor.comp_obj, eqToHom_app] at pg
  simpa [Scheme.Modules.pullbackCongr] using pg

/-- The left unitality of the pullback pseudofunctor, in componentwise form. -/
theorem pullbackComp_id_right_app (Y : U.Modules) :
    (Scheme.Modules.pullbackComp q (𝟙 U)).inv.app Y ≫
        (Scheme.Modules.pullback q).map ((Scheme.Modules.pullbackId U).hom.app Y) =
      (Scheme.Modules.pullbackCongr (Category.comp_id q)).hom.app Y := by
  have pg := NatTrans.congr_app (Scheme.Modules.pseudofunctor_left_unitality q) Y
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.leftUnitor_hom_app] at pg
  simp only [Functor.comp_obj, eqToHom_app] at pg
  simpa [Scheme.Modules.pullbackCongr] using pg

variable (e : U ⟶ V) (he : e ≫ q = 𝟙 U)

/-- For a section `e` of `q`, the canonical identification `e^* q^* ≅ 𝟭`. -/
noncomputable def sectionPullbackIso :
    Scheme.Modules.pullback q ⋙ Scheme.Modules.pullback e ≅ 𝟭 U.Modules :=
  Scheme.Modules.pullbackComp e q ≪≫ Scheme.Modules.pullbackCongr he ≪≫
    Scheme.Modules.pullbackId U

/-- Inverse image along a morphism with a section is faithful. -/
theorem pullback_map_injective (e' : U ⟶ V) (he' : e' ≫ q = 𝟙 U) {A B : U.Modules}
    {φ ψ : A ⟶ B}
    (h : (Scheme.Modules.pullback q).map φ = (Scheme.Modules.pullback q).map ψ) : φ = ψ := by
  have := Functor.Faithful.of_comp_iso (sectionPullbackIso q e' he')
  exact (Scheme.Modules.pullback q).map_injective h

/-- **The canonical comparison along a section.**  For a section `e` of `q`, the canonical
comparison of `(q ≫ e)^* q^*` with `𝟙^* q^*` is the inverse image along `q` of the
identification `e^* q^* ≅ 𝟭`. -/
theorem baseComparison_section_eq (Y : U.Modules) (h₃ : (q ≫ e) ≫ q = 𝟙 V ≫ q) :
    baseComparison q h₃ Y =
      (Scheme.Modules.pullbackComp q e).inv.app ((Scheme.Modules.pullback q).obj Y) ≫
        (Scheme.Modules.pullback q).map ((sectionPullbackIso q e he).hom.app Y) ≫
        (Scheme.Modules.pullbackId V).inv.app ((Scheme.Modules.pullback q).obj Y) := by
  have hE : q ≫ e ≫ q = q := by rw [he, Category.comp_id]
  have hF : q ≫ e ≫ q = q ≫ 𝟙 U := by rw [he]
  have hkey : (Scheme.Modules.pullbackComp q e).hom.app
          ((Scheme.Modules.pullback q).obj Y) ≫
        baseComparison q h₃ Y ≫
        (Scheme.Modules.pullbackId V).hom.app ((Scheme.Modules.pullback q).obj Y) =
      (Scheme.Modules.pullback q).map ((sectionPullbackIso q e he).hom.app Y) := by
    rw [baseComparison_eq, sectionPullbackIso]
    simp only [Iso.trans_hom, NatTrans.comp_app, Functor.map_comp, Category.assoc]
    rw [pullbackComp_id_left_app q Y, pullbackCongr_hom_app_comp,
      ← pullbackCongr_hom_app_comp (Category.assoc q e q) hE Y,
      ← reassoc_of% (map_pullbackComp_hom_app_comp q e q Y),
      ← pullbackCongr_hom_app_comp hF (Category.comp_id q) Y,
      ← pullbackComp_id_right_app q Y, ← pullbackComp_congr_app q he Y]
    simp
  calc baseComparison q h₃ Y
      = (Scheme.Modules.pullbackComp q e).inv.app ((Scheme.Modules.pullback q).obj Y) ≫
          ((Scheme.Modules.pullbackComp q e).hom.app ((Scheme.Modules.pullback q).obj Y) ≫
            baseComparison q h₃ Y ≫
            (Scheme.Modules.pullbackId V).hom.app ((Scheme.Modules.pullback q).obj Y)) ≫
          (Scheme.Modules.pullbackId V).inv.app ((Scheme.Modules.pullback q).obj Y) := by
        simp
    _ = _ := by rw [hkey]

/-- **Descent of morphisms along a morphism with a section.**  Let `q` have a section `e`, let
`a b : W ⟶ V` have equal composites with `q`, and let `d : V ⟶ W` satisfy `d ≫ a = q ≫ e` and
`d ≫ b = 𝟙`.  Then a morphism `φ : q^* A ⟶ q^* B` which commutes with the canonical comparisons
attached to `a` and `b` is the inverse image along `q` of a morphism `A ⟶ B`, namely of its own
restriction along the section. -/
theorem eq_pullback_map_of_baseComparison_comm {W : Scheme.{u}} {a b : W ⟶ V}
    (hab : a ≫ q = b ≫ q) (d : V ⟶ W) (hda : d ≫ a = q ≫ e) (hdb : d ≫ b = 𝟙 V)
    {A B : U.Modules}
    (φ : (Scheme.Modules.pullback q).obj A ⟶ (Scheme.Modules.pullback q).obj B)
    (hφ : baseComparison q hab A ≫ (Scheme.Modules.pullback b).map φ =
      (Scheme.Modules.pullback a).map φ ≫ baseComparison q hab B) :
    φ = (Scheme.Modules.pullback q).map
      ((sectionPullbackIso q e he).inv.app A ≫ (Scheme.Modules.pullback e).map φ ≫
        (sectionPullbackIso q e he).hom.app B) := by
  have h₃ : (q ≫ e) ≫ q = 𝟙 V ≫ q := by
    rw [Category.assoc, he, Category.comp_id, Category.id_comp]
  have hd : (d ≫ a) ≫ q = (d ≫ b) ≫ q := by rw [Category.assoc, Category.assoc, hab]
  -- Pull the hypothesis back along `d`.
  have h := congrArg (Scheme.Modules.pullback d).map hφ
  simp only [Functor.map_comp] at h
  rw [pullback_map_baseComparison d q hab A, pullback_map_baseComparison d q hab B,
    pullbackComp_naturality_map d b φ, pullbackComp_naturality_map d a φ] at h
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc] at h
  have hE0 : baseComparison q hd A ≫ (Scheme.Modules.pullback (d ≫ b)).map φ =
      (Scheme.Modules.pullback (d ≫ a)).map φ ≫ baseComparison q hd B := by
    have : Epi ((Scheme.Modules.pullbackComp d a).hom.app
        ((Scheme.Modules.pullback q).obj A)) := IsIso.epi_of_iso _
    have : Mono ((Scheme.Modules.pullbackComp d b).inv.app
        ((Scheme.Modules.pullback q).obj B)) := IsIso.mono_of_iso _
    rw [← cancel_epi ((Scheme.Modules.pullbackComp d a).hom.app
        ((Scheme.Modules.pullback q).obj A)),
      ← cancel_mono ((Scheme.Modules.pullbackComp d b).inv.app
        ((Scheme.Modules.pullback q).obj B))]
    simpa only [Category.assoc] using h
  -- Replace `d ≫ a` by `q ≫ e` and `d ≫ b` by `𝟙`.
  have hsplit : ∀ Y : U.Modules, baseComparison q hd Y =
      (Scheme.Modules.pullbackCongr hda).hom.app ((Scheme.Modules.pullback q).obj Y) ≫
        baseComparison q h₃ Y ≫
        (Scheme.Modules.pullbackCongr hdb.symm).hom.app
          ((Scheme.Modules.pullback q).obj Y) := by
    intro Y
    rw [pullbackCongr_hom_app_eq_baseComparison hda q Y,
      pullbackCongr_hom_app_eq_baseComparison hdb.symm q Y, baseComparison_comp,
      baseComparison_comp]
  have hnatA := (Scheme.Modules.pullbackCongr hda).hom.naturality φ
  have hnatB := (Scheme.Modules.pullbackCongr hdb.symm).hom.naturality φ
  rw [hsplit A, hsplit B] at hE0
  simp only [Category.assoc] at hE0
  rw [← hnatB, reassoc_of% hnatA] at hE0
  have hE : baseComparison q h₃ A ≫ (Scheme.Modules.pullback (𝟙 V)).map φ =
      (Scheme.Modules.pullback (q ≫ e)).map φ ≫ baseComparison q h₃ B := by
    have : Epi ((Scheme.Modules.pullbackCongr hda).hom.app
        ((Scheme.Modules.pullback q).obj A)) := IsIso.epi_of_iso _
    have : Mono ((Scheme.Modules.pullbackCongr hdb.symm).hom.app
        ((Scheme.Modules.pullback q).obj B)) := IsIso.mono_of_iso _
    rw [← cancel_epi ((Scheme.Modules.pullbackCongr hda).hom.app
        ((Scheme.Modules.pullback q).obj A)),
      ← cancel_mono ((Scheme.Modules.pullbackCongr hdb.symm).hom.app
        ((Scheme.Modules.pullback q).obj B))]
    simpa only [Category.assoc] using hE0
  -- Identify the two sides with the inverse image along `q` of the restriction along `e`.
  have hid' : (Scheme.Modules.pullback (𝟙 V)).map φ =
      (Scheme.Modules.pullbackId V).hom.app ((Scheme.Modules.pullback q).obj A) ≫ φ ≫
        (Scheme.Modules.pullbackId V).inv.app ((Scheme.Modules.pullback q).obj B) := by
    have hn := (Scheme.Modules.pullbackId V).hom.naturality φ
    simp only [Functor.id_map] at hn
    rw [← Category.assoc, ← hn]
    simp only [Iso.hom_inv_id_app, Category.assoc, Category.comp_id]
  have hcomp' : (Scheme.Modules.pullback (q ≫ e)).map φ =
      (Scheme.Modules.pullbackComp q e).inv.app ((Scheme.Modules.pullback q).obj A) ≫
        (Scheme.Modules.pullback q).map ((Scheme.Modules.pullback e).map φ) ≫
        (Scheme.Modules.pullbackComp q e).hom.app ((Scheme.Modules.pullback q).obj B) := by
    rw [pullbackComp_naturality_map q e φ]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [baseComparison_section_eq q e he A h₃, baseComparison_section_eq q e he B h₃, hid',
    hcomp'] at hE
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.hom_inv_id_app_assoc] at hE
  have hfinal : (Scheme.Modules.pullback q).map
        ((sectionPullbackIso q e he).hom.app A) ≫ φ =
      (Scheme.Modules.pullback q).map ((Scheme.Modules.pullback e).map φ) ≫
        (Scheme.Modules.pullback q).map ((sectionPullbackIso q e he).hom.app B) := by
    have : Epi ((Scheme.Modules.pullbackComp q e).inv.app
        ((Scheme.Modules.pullback q).obj A)) := IsIso.epi_of_iso _
    have : Mono ((Scheme.Modules.pullbackId V).inv.app
        ((Scheme.Modules.pullback q).obj B)) := IsIso.mono_of_iso _
    rw [← cancel_epi ((Scheme.Modules.pullbackComp q e).inv.app
        ((Scheme.Modules.pullback q).obj A)),
      ← cancel_mono ((Scheme.Modules.pullbackId V).inv.app
        ((Scheme.Modules.pullback q).obj B))]
    simpa only [Category.assoc] using hE
  have hiso : IsIso ((Scheme.Modules.pullback q).map
      ((sectionPullbackIso q e he).hom.app A)) := Functor.map_isIso _ _
  have hepi : Epi ((Scheme.Modules.pullback q).map
      ((sectionPullbackIso q e he).hom.app A)) := IsIso.epi_of_iso _
  rw [← cancel_epi ((Scheme.Modules.pullback q).map ((sectionPullbackIso q e he).hom.app A)),
    Functor.map_comp, Functor.map_comp, ← Category.assoc, ← Functor.map_comp,
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  exact hfinal

end Section


variable {S : Scheme.{u}} (G : GroupoidScheme S)

/-- Forgetting the groupoid descent datum, as a functor to quasi-coherent modules on the
object scheme. -/
noncomputable def quasicoherentForget :
    QuasicoherentModule G ⥤
      (SheafOfModules.isQuasicoherent G.objects.left.ringCatSheaf).FullSubcategory :=
  ObjectProperty.lift (SheafOfModules.isQuasicoherent G.objects.left.ringCatSheaf)
    (QuasicoherentModule.forget G) (fun M => M.isQuasicoherent)

/-- **The cocycle condition, rearranged.**  On the scheme of composable arrows, applying the
descent morphism to the second arrow and then the inverse of its reindexing along the
composition law is the inverse of its reindexing along the first projection, up to the
canonical comparisons of inverse images along equal morphisms. -/
theorem reindexHom_cocycle_inv (M : QuasicoherentModule G) :
    reindexHom (pullback.snd G.source G.target).left M.alpha ≫
        (Scheme.Modules.pullbackCongr
          (congrArg Over.Hom.left G.source_comp).symm).hom.app M.module ≫
        reindexHom G.comp.left (inv M.alpha) =
      (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left
            (pullback.condition : pullback.fst G.source G.target ≫ G.source =
              pullback.snd G.source G.target ≫ G.target)).symm).hom.app M.module ≫
        reindexHom (pullback.fst G.source G.target).left (inv M.alpha) ≫
        (Scheme.Modules.pullbackCongr
          (congrArg Over.Hom.left G.target_comp).symm).hom.app M.module :=
  cocycle_rearrange _ _ _ _ _ _ _ _ _ _ M.cocycle
    (by rw [pullbackCongr_hom_app_comp]; simp)
    (by rw [pullbackCongr_hom_app_comp]; simp)
    (by simp) (by simp)

/-- **The cocycle condition in the form the coinduction adjunction uses.**  The two ways of
transporting the descent morphism of a quasi-coherent module to the scheme of composable
arrows agree:  applying it to the second arrow and then inverting it on the composite is the
same as inverting it on the first arrow, measured against the comparisons of the two composite
inverse images around the two cartesian squares of the composition diagram. -/
theorem alpha_pullbackSquareIso (M : QuasicoherentModule G) :
    (Scheme.Modules.pullback (pullback.snd G.source G.target).left).map M.alpha ≫
        (Stacks.Modules.pullbackSquareIso G.source.left
            (pullback.snd G.source G.target).left G.source.left G.comp.left
            (isPullback_comp_snd_source G).w).hom.app M.module ≫
        (Scheme.Modules.pullback G.comp.left).map (inv M.alpha) =
      (Stacks.Modules.pullbackSquareIso G.source.left
            (pullback.snd G.source G.target).left G.target.left
            (pullback.fst G.source G.target).left
            (isPullback_composableArrows G).w).hom.app M.module ≫
        (Scheme.Modules.pullback (pullback.fst G.source G.target).left).map (inv M.alpha) ≫
        (coinductionComparison G).hom.app M.module := by
  rw [pullback_map_eq_reindexHom, pullback_map_eq_reindexHom, pullback_map_eq_reindexHom,
    Stacks.Modules.pullbackSquareIso, Stacks.Modules.pullbackSquareIso, coinductionComparison]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc,
    Iso.inv_hom_id_app_assoc]
  rw [reassoc_of% reindexHom_cocycle_inv G M]

/-- The canonical identification `e^* t^* ≅ 𝟭` coming from `e ≫ t = 𝟙`. -/
noncomputable def targetSectionIso :
    Scheme.Modules.pullback G.target.left ⋙ Scheme.Modules.pullback G.identity.left ≅
      𝟭 G.objects.left.Modules :=
  sectionPullbackIso G.target.left G.identity.left (identity_left_comp_target_left G)

/-- Restriction along the identity section:  a morphism between the inverse images along the
target of two modules on the object scheme restricts to a morphism between the modules. -/
noncomputable def restrictAlongIdentity {F F' : G.objects.left.Modules}
    (θ : (Scheme.Modules.pullback G.target.left).obj F ⟶
      (Scheme.Modules.pullback G.target.left).obj F') : F ⟶ F' :=
  (targetSectionIso G).inv.app F ≫ (Scheme.Modules.pullback G.identity.left).map θ ≫
    (targetSectionIso G).hom.app F'

/-- Restriction along the identity section undoes the inverse image along the target. -/
@[simp]
theorem restrictAlongIdentity_map {F F' : G.objects.left.Modules} (f : F ⟶ F') :
    restrictAlongIdentity G ((Scheme.Modules.pullback G.target.left).map f) = f := by
  have hn := (targetSectionIso G).hom.naturality f
  simp only [Functor.comp_map, Functor.id_map] at hn
  rw [restrictAlongIdentity, hn, Iso.inv_hom_id_app_assoc]

/-- The comparison `pr_0^* t^* ≅ c^* t^*` is the canonical comparison attached to the equality
`pr_0 ≫ t = c ≫ t`. -/
theorem coinductionComparison_hom_app_eq (Y : G.objects.left.Modules) :
    (coinductionComparison G).hom.app Y =
      baseComparison G.target.left
        ((congrArg Over.Hom.left G.target_comp).symm :
          (pullback.fst G.source G.target).left ≫ G.target.left =
            G.comp.left ≫ G.target.left) Y :=
  rfl

/-- The underlying module functor of coinduction, `𝒢 ↦ s_* t^* 𝒢`, on quasi-coherent
modules. -/
noncomputable def coinductionModule :
    (SheafOfModules.isQuasicoherent G.objects.left.ringCatSheaf).FullSubcategory ⥤
      G.objects.left.Modules :=
  (SheafOfModules.isQuasicoherent G.objects.left.ringCatSheaf).ι ⋙
    Scheme.Modules.pullback G.target.left ⋙ Scheme.Modules.pushforward G.source.left

/-- The underlying module functor of coinduction sends `𝒢` to `s_* t^* 𝒢`. -/
@[simp]
theorem coinductionModule_obj
    (N : (SheafOfModules.isQuasicoherent G.objects.left.ringCatSheaf).FullSubcategory) :
    (coinductionModule G).obj N = (Scheme.Modules.pushforward G.source.left).obj
      ((Scheme.Modules.pullback G.target.left).obj N.obj) :=
  rfl

section Coinduction

variable [Flat G.source.left] [Flat G.target.left]
  [QuasiCompact G.source.left] [QuasiSeparated G.source.left]

/-- **Descent compatibility across the transpose.**  A morphism `u : s^* 𝓕 ⟶ t^* 𝒢` has a
transpose along `s` which intertwines the descent morphism of `𝓕` with the canonical descent
morphism of `s_* t^* 𝒢` exactly when `u` satisfies the displayed condition on the scheme of
composable arrows.  This is the coinduction analogue of
`Stacks.Groupoids.GroupoidScheme.pushforwardDescent_comm_iff`. -/
alias coinduction_comm_iff := comm_iff

/-- **The transpose of a morphism of modules is descent-compatible.**  For a quasi-coherent
module `(𝓕, α)` on the groupoid scheme and a morphism `f : 𝓕 ⟶ 𝒢` of modules on the object
scheme, the adjunct along `s` of `α^{-1}` followed by `t^* f` intertwines `α` with the
canonical descent morphism of `s_* t^* 𝒢`. -/
theorem coinduction_comm (M : QuasicoherentModule G) (𝒢 : G.objects.left.Modules)
    [𝒢.IsQuasicoherent] (f : M.module ⟶ 𝒢) :
    M.alpha ≫ (Scheme.Modules.pullback G.source.left).map
        ((Scheme.Modules.pullbackPushforwardAdjunction G.source.left).homEquiv M.module
          ((Scheme.Modules.pullback G.target.left).obj 𝒢)
          (inv M.alpha ≫ (Scheme.Modules.pullback G.target.left).map f)) =
      (Scheme.Modules.pullback G.target.left).map
          ((Scheme.Modules.pullbackPushforwardAdjunction G.source.left).homEquiv M.module
            ((Scheme.Modules.pullback G.target.left).obj 𝒢)
            (inv M.alpha ≫ (Scheme.Modules.pullback G.target.left).map f)) ≫
        (coinductionAlpha G 𝒢).hom :=
  (coinduction_comm_iff G M 𝒢 _).2 (by
    simp only [Functor.map_comp, Category.assoc]
    rw [← coinductionComparison_naturality G f, reassoc_of% alpha_pullbackSquareIso G M])

/-- The coinduction functor `𝒢 ↦ (s_* t^* 𝒢, α)`. -/
noncomputable def coinduction :
    (SheafOfModules.isQuasicoherent G.objects.left.ringCatSheaf).FullSubcategory ⥤
      QuasicoherentModule G where
  obj N :=
    { module := (Scheme.Modules.pushforward G.source.left).obj
        ((Scheme.Modules.pullback G.target.left).obj N.obj)
      isQuasicoherent := isQuasicoherent_pushforwardSource_pullbackTarget G N.obj
      alpha := (coinductionAlpha G N.obj).hom
      cocycle := cocycle_coinductionAlpha G N.obj
      identity := identity_coinductionAlpha G N.obj }
  map f :=
    { hom := (coinductionModule G).map f
      comm := coinductionAlpha_naturality G f.hom }
  map_id N := QuasicoherentModule.Hom.ext ((coinductionModule G).map_id N)
  map_comp f g := QuasicoherentModule.Hom.ext ((coinductionModule G).map_comp f g)

/-- The underlying module of the coinduction of `𝒢` is `s_* t^* 𝒢`. -/
@[simp]
theorem coinduction_obj_module
    (N : (SheafOfModules.isQuasicoherent G.objects.left.ringCatSheaf).FullSubcategory) :
    ((coinduction G).obj N).module = (Scheme.Modules.pushforward G.source.left).obj
      ((Scheme.Modules.pullback G.target.left).obj N.obj) :=
  rfl

/-- The descent morphism of the coinduction of `𝒢` is `coinductionAlpha`. -/
@[simp]
theorem coinduction_obj_alpha
    (N : (SheafOfModules.isQuasicoherent G.objects.left.ringCatSheaf).FullSubcategory) :
    ((coinduction G).obj N).alpha = (coinductionAlpha G N.obj).hom :=
  rfl

/-! ### The transpose -/

/-- The transpose on underlying modules:  compose the inverse descent morphism with `t^* f`
and take the adjunct along the source. -/
noncomputable def coinductionTransposeHom (M : QuasicoherentModule G)
    (𝒢 : G.objects.left.Modules) (f : M.module ⟶ 𝒢) :
    M.module ⟶ (Scheme.Modules.pushforward G.source.left).obj
      ((Scheme.Modules.pullback G.target.left).obj 𝒢) :=
  (Scheme.Modules.pullbackPushforwardAdjunction G.source.left).homEquiv M.module
    ((Scheme.Modules.pullback G.target.left).obj 𝒢)
    (inv M.alpha ≫ (Scheme.Modules.pullback G.target.left).map f)

omit [Flat G.source.left] [Flat G.target.left]
    [QuasiCompact G.source.left] [QuasiSeparated G.source.left] in
/-- The inverse descent morphisms intertwine a morphism of quasi-coherent modules on the
groupoid scheme. -/
theorem alpha_inv_comm {M N : QuasicoherentModule G} (k : M ⟶ N) :
    inv M.alpha ≫ (Scheme.Modules.pullback G.target.left).map
        (QuasicoherentModule.Hom.hom k) =
      (Scheme.Modules.pullback G.source.left).map (QuasicoherentModule.Hom.hom k) ≫
        inv N.alpha := by
  rw [IsIso.inv_comp_eq, ← Category.assoc, IsIso.eq_comp_inv]
  exact k.comm.symm

omit [Flat G.source.left] [Flat G.target.left]
    [QuasiCompact G.source.left] [QuasiSeparated G.source.left] in
/-- The transpose is natural in the module on the object scheme. -/
theorem coinductionTransposeHom_comp_right (M : QuasicoherentModule G)
    (𝒢 𝒢' : G.objects.left.Modules) (f : M.module ⟶ 𝒢) (g : 𝒢 ⟶ 𝒢') :
    coinductionTransposeHom G M 𝒢' (f ≫ g) =
      coinductionTransposeHom G M 𝒢 f ≫ (Scheme.Modules.pushforward G.source.left).map
        ((Scheme.Modules.pullback G.target.left).map g) := by
  rw [coinductionTransposeHom, coinductionTransposeHom, Functor.map_comp, ← Category.assoc,
    Adjunction.homEquiv_naturality_right]

omit [Flat G.source.left] [Flat G.target.left]
    [QuasiCompact G.source.left] [QuasiSeparated G.source.left] in
/-- The transpose is natural in the quasi-coherent module on the groupoid scheme. -/
theorem coinductionTransposeHom_comp_left {M M' : QuasicoherentModule G} (k : M' ⟶ M)
    (𝒢 : G.objects.left.Modules) (f : M.module ⟶ 𝒢) :
    coinductionTransposeHom G M' 𝒢 (QuasicoherentModule.Hom.hom k ≫ f) =
      QuasicoherentModule.Hom.hom k ≫ coinductionTransposeHom G M 𝒢 f := by
  rw [coinductionTransposeHom, coinductionTransposeHom, Functor.map_comp, ← Category.assoc,
    alpha_inv_comm G k, Category.assoc, ← Adjunction.homEquiv_naturality_left]

omit [Flat G.source.left] [Flat G.target.left]
    [QuasiCompact G.source.left] [QuasiSeparated G.source.left] in
/-- **The unit formula of Tag 0GNF.**  The transpose of the identity is the unit of the
pullback--pushforward adjunction along the source followed by the direct image of the inverse
descent morphism. -/
theorem coinductionTransposeHom_id (M : QuasicoherentModule G) :
    coinductionTransposeHom G M M.module (𝟙 M.module) =
      (Scheme.Modules.pullbackPushforwardAdjunction G.source.left).unit.app M.module ≫
        (Scheme.Modules.pushforward G.source.left).map (inv M.alpha) := by
  rw [coinductionTransposeHom, CategoryTheory.Functor.map_id, Category.comp_id,
    Adjunction.homEquiv_unit]

/-- **The adjunction correspondence of Tag 07TR, forward direction.**  A morphism
`f : 𝓕 ⟶ 𝒢` of quasi-coherent modules on the object scheme transposes to a morphism of
quasi-coherent modules on the groupoid scheme `(𝓕, α) ⟶ (s_* t^* 𝒢, α_𝒢)`. -/
noncomputable def coinductionTranspose (M : QuasicoherentModule G)
    (N : (SheafOfModules.isQuasicoherent G.objects.left.ringCatSheaf).FullSubcategory)
    (f : (quasicoherentForget G).obj M ⟶ N) : M ⟶ (coinduction G).obj N where
  hom := coinductionTransposeHom G M N.obj f.hom
  comm := coinduction_comm G M N.obj f.hom

/-- **The characterising equation of the transpose.** -/
@[simp]
theorem coinductionTranspose_hom (M : QuasicoherentModule G)
    (N : (SheafOfModules.isQuasicoherent G.objects.left.ringCatSheaf).FullSubcategory)
    (f : (quasicoherentForget G).obj M ⟶ N) :
    (coinductionTranspose G M N f).hom =
      (Scheme.Modules.pullbackPushforwardAdjunction G.source.left).homEquiv M.module
        ((Scheme.Modules.pullback G.target.left).obj N.obj)
        (inv M.alpha ≫ (Scheme.Modules.pullback G.target.left).map f.hom) :=
  rfl

/-- The transpose is natural in the quasi-coherent module on the groupoid scheme. -/
theorem coinductionTranspose_naturality_left {M M' : QuasicoherentModule G} (k : M' ⟶ M)
    (N : (SheafOfModules.isQuasicoherent G.objects.left.ringCatSheaf).FullSubcategory)
    (f : (quasicoherentForget G).obj M ⟶ N) :
    coinductionTranspose G M' N ((quasicoherentForget G).map k ≫ f) =
      k ≫ coinductionTranspose G M N f :=
  QuasicoherentModule.Hom.ext (coinductionTransposeHom_comp_left G k N.obj f.hom)

/-- The transpose is natural in the quasi-coherent module on the object scheme. -/
theorem coinductionTranspose_naturality_right (M : QuasicoherentModule G)
    {N N' : (SheafOfModules.isQuasicoherent G.objects.left.ringCatSheaf).FullSubcategory}
    (f : (quasicoherentForget G).obj M ⟶ N) (g : N ⟶ N') :
    coinductionTranspose G M N' (f ≫ g) =
      coinductionTranspose G M N f ≫ (coinduction G).map g :=
  QuasicoherentModule.Hom.ext (coinductionTransposeHom_comp_right G M N.obj N'.obj f.hom g.hom)

/-- **The unit formula of Tag 0GNF, for the transpose.** -/
theorem coinductionTranspose_id_hom (M : QuasicoherentModule G) :
    (coinductionTranspose G M ((quasicoherentForget G).obj M) (𝟙 _)).hom =
      (Scheme.Modules.pullbackPushforwardAdjunction G.source.left).unit.app M.module ≫
        (Scheme.Modules.pushforward G.source.left).map (inv M.alpha) :=
  coinductionTransposeHom_id G M

end Coinduction



/-! ### The adjunction and the unit -/

section Adjunction

variable {S : Scheme.{u}} (G : GroupoidScheme S)
  [Flat G.source.left] [Flat G.target.left]
  [QuasiCompact G.source.left] [QuasiSeparated G.source.left]

/-- **The hom-set bijection of Tag 07TR.**  Morphisms `𝓕 ⟶ 𝒢` of quasi-coherent modules on the
object scheme correspond to morphisms `(𝓕, α) ⟶ (s_* t^* 𝒢, α_𝒢)` of quasi-coherent modules on
the groupoid scheme. -/
noncomputable def coinductionHomEquiv (M : QuasicoherentModule G)
    (N : (SheafOfModules.isQuasicoherent G.objects.left.ringCatSheaf).FullSubcategory) :
    ((quasicoherentForget G).obj M ⟶ N) ≃ (M ⟶ (coinduction G).obj N) where
  toFun f := coinductionTranspose G M N f
  invFun g := ObjectProperty.homMk (untranspose G M N.obj g.hom)
  left_inv f := by
    apply ObjectProperty.hom_ext
    change untranspose G M N.obj (coinductionTranspose G M N f).hom = f.hom
    simpa [coinductionTranspose_hom, transpose] using untranspose_transpose G M N.obj f.hom
  right_inv g := QuasicoherentModule.Hom.ext (transpose_untranspose G M N.obj g.hom g.comm)

/-- **Coinduction is right adjoint to forgetting a groupoid descent datum.**  This is the
adjunction of Tag 07TR. -/
@[stacks 07TR "the right adjointness of the coinduction functor to the forgetful functor"]
noncomputable def coinductionAdjunction : quasicoherentForget G ⊣ coinduction G :=
  Adjunction.mkOfHomEquiv
    { homEquiv := coinductionHomEquiv G
      homEquiv_naturality_left_symm := fun {M' M N} k g => by
        rw [Equiv.symm_apply_eq]
        have h := coinductionTranspose_naturality_left G k N
          ((coinductionHomEquiv G M N).symm g)
        rw [show coinductionTranspose G M N ((coinductionHomEquiv G M N).symm g) = g from
          (coinductionHomEquiv G M N).apply_symm_apply g] at h
        exact h.symm
      homEquiv_naturality_right := fun {M N N'} f g =>
        coinductionTranspose_naturality_right G M f g }

/-- **Stacks 0GNF.**  The unit of the forgetful--coinduction adjunction at a quasi-coherent
module `(𝓕, α)` on a groupoid scheme is, on underlying modules, the unit of the
pullback--pushforward adjunction along the source followed by the direct image of the inverse
of the descent morphism:
`𝓕 ⟶ s_* s^* 𝓕 ⟶ s_* t^* 𝓕`. -/
@[stacks 0GNF]
theorem coinductionAdjunction_unit_app (M : QuasicoherentModule G) :
    ((coinductionAdjunction G).unit.app M).hom =
      (Scheme.Modules.pullbackPushforwardAdjunction G.source.left).unit.app M.module ≫
        (Scheme.Modules.pushforward G.source.left).map (inv M.alpha) := by
  have key : (coinductionAdjunction G).homEquiv M ((quasicoherentForget G).obj M) (𝟙 _) =
      (coinductionAdjunction G).unit.app M := by
    rw [Adjunction.homEquiv_unit]
    simp
  have hdef : (coinductionAdjunction G).homEquiv M ((quasicoherentForget G).obj M) (𝟙 _) =
      coinductionTranspose G M ((quasicoherentForget G).obj M) (𝟙 _) := by
    simp [coinductionAdjunction, coinductionHomEquiv]
  rw [← key, hdef, coinductionTranspose_id_hom]

end Adjunction

end Stacks.Groupoids.GroupoidScheme

end
