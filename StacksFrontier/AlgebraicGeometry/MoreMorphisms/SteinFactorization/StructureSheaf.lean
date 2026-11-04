module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.Proper

/-!
# The structure sheaf of the relative normalization

Let `f : X ⟶ S` be a universally closed, quasi-separated morphism of schemes and let
`S' = f.normalization` be the normalization of `S` in `X`, so that `f` factors as
`X --f'--> S' --π--> S` with `f' = f.toNormalization` and `π = f.fromNormalization`.  This file
proves that the canonical map `𝒪_{S'} ⟶ f'_*𝒪_X` is an isomorphism, i.e. that
`f'_*𝒪_X = 𝒪_{S'}`.

Over an affine open `U ⊆ S` the sections of `S'` are the integral closure of `Γ(S, U)` in
`Γ(X, f⁻¹U)`, and that integral closure is everything because `f` is universally closed; this
gives the assertion on the opens `π⁻¹U`.  The basic opens of these affine opens form a basis of
`S'`, and on a basic open both sides are the same localization — the right-hand side by the
qcqs lemma `AlgebraicGeometry.isLocalization_basicOpen_of_qcqs` — so the map is an isomorphism
on a basis, hence an isomorphism of sheaves.

## Main results

* `Stacks.AlgebraicGeometry.isIntegral_app_of_universallyClosed`: for a universally closed
  morphism and an affine open `U` of the target, `Γ(S, U) ⟶ Γ(X, f⁻¹U)` is an integral ring map.
* `Stacks.AlgebraicGeometry.isIso_app_basicOpen`: if `g.app U` is an isomorphism for an affine
  open `U` with qcqs preimage, then so is `g.app (Y.basicOpen r)` for every `r : Γ(Y, U)`.
* `Stacks.AlgebraicGeometry.isIso_c_of_isIso_app_basicOpen`: a morphism of schemes whose
  sections map is an isomorphism on the basic opens of an affine cover of the target induces an
  isomorphism `𝒪_Y ⟶ g_*𝒪_X`.
* `Stacks.SteinFactorization.isIso_app_toNormalization`: the sections of the relative
  normalization over `π⁻¹U` agree with the sections of `X` over `f⁻¹U`.
* `Stacks.SteinFactorization.isIso_c_toNormalization`: clause (3) of [Stacks, Tag 03GY], that
  `f'_*𝒪_X = 𝒪_{S'}`.
* `Stacks.SteinFactorization.isIso_c_toNormalization_of_isProper`: the same clause of
  [Stacks, Tag 03H2], for a proper morphism.

## References

* [Stacks Project, Tag 03GY](https://stacks.math.columbia.edu/tag/03GY)
* [Stacks Project, Tag 03H2](https://stacks.math.columbia.edu/tag/03H2)
* [Stacks Project, Tag 035H](https://stacks.math.columbia.edu/tag/035H)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.AlgebraicGeometry

/-- For a universally closed morphism `f : X ⟶ Y` and an affine open `U ⊆ Y`, the ring map
`Γ(Y, U) ⟶ Γ(X, f⁻¹U)` is integral.  This is the affine-open form of
`AlgebraicGeometry.isIntegral_appTop_of_universallyClosed`, obtained from it by restricting `f`
over `U`. -/
public theorem isIntegral_app_of_universallyClosed {X Y : Scheme.{u}} (f : X ⟶ Y)
    [UniversallyClosed f] {U : Y.Opens} (hU : IsAffineOpen U) : (f.app U).hom.IsIntegral := by
  have : IsAffine U.toScheme := hU
  have hr : UniversallyClosed (f.resLE U (f ⁻¹ᵁ U) le_rfl) := by
    rw [Scheme.Hom.resLE_eq_morphismRestrict]
    infer_instance
  have h := isIntegral_appTop_of_universallyClosed (f.resLE U (f ⁻¹ᵁ U) le_rfl)
  rwa [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, Scheme.Hom.appLE_eq_app,
    CommRingCat.hom_comp, RingHom.isIntegral_respectsIso.cancel_left_isIso,
    CommRingCat.hom_comp, RingHom.isIntegral_respectsIso.cancel_right_isIso] at h

/-- Let `g : X ⟶ Y` be a morphism of schemes and let `U ⊆ Y` be an affine open whose preimage is
quasi-compact and quasi-separated.  If `Γ(Y, U) ⟶ Γ(X, g⁻¹U)` is an isomorphism, then so is
`Γ(Y, Y.basicOpen r) ⟶ Γ(X, g⁻¹(Y.basicOpen r))` for every section `r` over `U`: both sides are
the localization away from `r`, the target by the qcqs lemma. -/
public theorem isIso_app_basicOpen {X Y : Scheme.{u}} (g : X ⟶ Y) {U : Y.Opens}
    (hU : IsAffineOpen U) (hc : IsCompact (g ⁻¹ᵁ U).1) (hqs : IsQuasiSeparated (g ⁻¹ᵁ U).1)
    [IsIso (g.app U)] (r : Γ(Y, U)) : IsIso (g.app (Y.basicOpen r)) := by
  have h₁ := hU.isLocalization_basicOpen r
  have h₂ := isLocalization_basicOpen_of_qcqs hc hqs (g.app U r)
  have hbij : Function.Bijective (g.app U).hom := ConcreteCategory.bijective_of_isIso _
  have key : g.app (Y.basicOpen r) =
      CommRingCat.ofHom (IsLocalization.Away.map Γ(Y, Y.basicOpen r)
        Γ(X, X.basicOpen (g.app U r)) (g.app U).hom r)
        ≫ X.presheaf.map (eqToHom (by simp)).op := by
    ext : 1
    apply IsLocalization.ringHom_ext (.powers r)
    rw [IsLocalization.Away.map, CommRingCat.hom_comp, RingHom.comp_assoc, CommRingCat.hom_ofHom,
      IsLocalization.map_comp, RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra,
      ← RingHom.comp_assoc, ← CommRingCat.hom_comp, ← CommRingCat.hom_comp, ← X.presheaf.map_comp]
    simp
  have hb : Function.Bijective (IsLocalization.Away.map Γ(Y, Y.basicOpen r)
      Γ(X, X.basicOpen (g.app U r)) (g.app U).hom r) := by
    refine ⟨?_, ?_⟩
    · rw [IsLocalization.Away.map_injective_iff]
      exact fun a ha ↦ ⟨0, by simpa using hbij.1 (ha.trans (map_zero _).symm)⟩
    · rw [IsLocalization.Away.map_surjective_iff]
      intro a
      obtain ⟨b, hb⟩ := hbij.2 a
      exact ⟨b, 0, by simpa using hb⟩
  have : IsIso (CommRingCat.ofHom (IsLocalization.Away.map Γ(Y, Y.basicOpen r)
      Γ(X, X.basicOpen (g.app U r)) (g.app U).hom r)) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact hb
  rw [key]
  infer_instance

/-- A morphism `g : X ⟶ Y` of schemes for which `Γ(Y, V) ⟶ Γ(X, g⁻¹V)` is an isomorphism for
every basic open `V` of every member of an affine open cover of `Y` satisfies `g_*𝒪_X = 𝒪_Y`:
such basic opens form a basis of `Y`, and a morphism of sheaves that is an isomorphism on a
basis is an isomorphism. -/
public theorem isIso_c_of_isIso_app_basicOpen {X Y : Scheme.{u}} (g : X ⟶ Y) {ι : Type*}
    (V : ι → Y.Opens) (hV : ∀ i, IsAffineOpen (V i)) (hcov : ⨆ i, V i = ⊤)
    (h : ∀ (i : ι) (r : Γ(Y, V i)), IsIso (g.app (Y.basicOpen r))) : IsIso g.c := by
  let B : (Σ i : ι, Γ(Y, V i)) → Y.Opens := fun p ↦ Y.basicOpen p.2
  have hB : Opens.IsBasis (Set.range B) := by
    rw [Opens.isBasis_iff_nbhd]
    intro W x hx
    obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp (hcov ▸ trivial : x ∈ (⨆ i, V i : Y.Opens))
    obtain ⟨r, hr₁, hr₂⟩ := (hV i).exists_basicOpen_le (V := W) ⟨x, hx⟩ hxi
    exact ⟨B ⟨i, r⟩, ⟨⟨i, r⟩, rfl⟩, hr₂, hr₁⟩
  let φ : Y.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat g.base).obj X.sheaf := ⟨g.c⟩
  have : IsIso φ := TopCat.Sheaf.isIso_iff_isIso_basis hB (φ := φ) fun p ↦ h p.1 p.2
  exact (inferInstance : IsIso ((TopCat.Sheaf.forget CommRingCat Y).map φ))

end Stacks.AlgebraicGeometry

namespace Stacks.SteinFactorization

variable {X S : Scheme.{u}} (f : X ⟶ S) [UniversallyClosed f] [QuasiSeparated f]

/-- **Stacks Project, Tag 03GY.**  For a universally closed, quasi-separated morphism
`f : X ⟶ S` and an affine open `U ⊆ S`, the canonical map from the sections of the normalization
of `S` in `X` over `π⁻¹U` to the sections of `X` over `f⁻¹U` is an isomorphism: the former are
the integral closure of `Γ(S, U)` in `Γ(X, f⁻¹U)`, and `Γ(X, f⁻¹U)` is already integral over
`Γ(S, U)`. -/
public theorem isIso_app_toNormalization {U : S.Opens} (hU : IsAffineOpen U) :
    IsIso (f.toNormalization.app (f.fromNormalization ⁻¹ᵁ U)) := by
  let _ : Algebra ↑Γ(S, U) ↑Γ(X, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
  have : Algebra.IsIntegral ↑Γ(S, U) ↑Γ(X, f ⁻¹ᵁ U) := by
    rw [← algebraMap_isIntegral_iff, RingHom.algebraMap_toAlgebra]
    exact Stacks.AlgebraicGeometry.isIntegral_app_of_universallyClosed f hU
  have hval : IsIso (CommRingCat.ofHom
      (Subalgebra.val (integralClosure ↑Γ(S, U) ↑Γ(X, f ⁻¹ᵁ U))).toRingHom) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact ⟨Subtype.val_injective, fun x ↦ ⟨⟨x, (mem_integralClosure_iff _ _).mpr
      (Algebra.IsIntegral.isIntegral x)⟩, rfl⟩⟩
  have key : IsIso (f.toNormalization.appLE (f.fromNormalization ⁻¹ᵁ U) (f ⁻¹ᵁ U)
      (by simp [← Scheme.Hom.comp_preimage])) := by
    rw [← f.normalizationObjIso_hom_val hU]
    infer_instance
  rw [Scheme.Hom.app_eq_appLE]
  exact (Scheme.Hom.appLE_congr _ le_rfl rfl (by simp [← Scheme.Hom.comp_preimage])
    fun g ↦ IsIso g).mpr key

/-- **Stacks Project, Tag 03GY.**  Clause (3) of the factorization of a universally closed,
quasi-separated morphism `f : X ⟶ S`: the canonical map from the structure sheaf of the
normalization `S'` of `S` in `X` to the pushforward of the structure sheaf of `X` along the
first map `f' : X ⟶ S'` is an isomorphism, that is, `f'_*𝒪_X = 𝒪_{S'}`. -/
@[stacks 03GY "pushforward_structure_sheaf"]
public theorem isIso_c_toNormalization : IsIso f.toNormalization.c := by
  refine Stacks.AlgebraicGeometry.isIso_c_of_isIso_app_basicOpen _
    (fun U : S.affineOpens ↦ f.fromNormalization ⁻¹ᵁ U.1)
    (fun U ↦ U.2.preimage f.fromNormalization)
    (f.fromNormalization.iSup_preimage_eq_top (iSup_affineOpens_eq_top S)) fun U r ↦ ?_
  have := isIso_app_toNormalization f U.2
  exact Stacks.AlgebraicGeometry.isIso_app_basicOpen _ (U.2.preimage f.fromNormalization)
    (f.toNormalization.isCompact_preimage (f.fromNormalization.isCompact_preimage U.2.isCompact))
    (f.toNormalization.isQuasiSeparated_preimage
      (f.fromNormalization.isQuasiSeparated_preimage U.2.isQuasiSeparated)) r

/-- **Stacks Project, Tag 03H2.**  Clause (3) of the factorization of a proper morphism
`f : X ⟶ S`: the pushforward of the structure sheaf of `X` along the first map
`f' : X ⟶ f.normalization` is the structure sheaf of `f.normalization`. -/
@[stacks 03H2 "structure_sheaf_pushforward"]
public theorem isIso_c_toNormalization_of_isProper {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] :
    IsIso f.toNormalization.c :=
  isIso_c_toNormalization f

end Stacks.SteinFactorization
