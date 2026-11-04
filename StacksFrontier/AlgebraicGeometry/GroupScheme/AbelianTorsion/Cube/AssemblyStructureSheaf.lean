module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ProperGlobalSections
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.CubeRelation

/-!
# The structure sheaf of a base is the direct image of the structure sheaf of a product

Let `S` be an affine scheme, `f : X ⟶ S` quasi-compact and quasi-separated with
`Γ(S, 𝒪_S) ⟶ Γ(X, 𝒪_X)` an isomorphism, and `g : T ⟶ S` flat. Then for the projection
`p : X ×_S T ⟶ T` the map `𝒪_T ⟶ p_*𝒪_{X ×_S T}` is an isomorphism: on a quasi-compact
quasi-separated open `V ⊆ T`, flat base change in degree zero
([Stacks, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH); Mathlib's
`AlgebraicGeometry.isIso_pushoutSection_of_isCompact_of_flat_right_of_ringHomFlat`) identifies
`Γ(X ×_S V, 𝒪)` with `Γ(X, 𝒪) ⊗_{Γ(S, 𝒪)} Γ(V, 𝒪) = Γ(V, 𝒪)`, and the affine opens form a basis.

This is the input `𝒪_Z = p_*𝒪_P` of the last step of the proof of the theorem of the cube over a
field (step 4 of the cube proof), for `P = (A × A) × A ⟶ Z = A` with `A` an abelian variety,
where `Γ(A × A, 𝒪) = k` is the same statement applied once more.

## Main results

* `Stacks.Groupoids.isIso_app_pullback_snd_of_isIso_appTop`: the sections over a qcqs open.
* `Stacks.Groupoids.isIso_structureSheafHom_pullback_snd_of_isIso_appTop`: `𝒪_T ≅ p_*𝒪`.
* `Stacks.Groupoids.isIso_structureSheafHom_cubeProj₃`: the case of `A × A × A ⟶ A`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
  CartesianMonoidalCategory TopologicalSpace Opposite

universe u

namespace Stacks.Groupoids

/-- **Degree-zero flat base change of `Γ(X, 𝒪) = Γ(S, 𝒪)`, over a qcqs open.** For `S` affine,
`f : X ⟶ S` qcqs with `Γ(S, 𝒪) ≅ Γ(X, 𝒪)` and `g : T ⟶ S` flat, the projection
`p : X ×_S T ⟶ T` induces an isomorphism `Γ(V, 𝒪_T) ≅ Γ(p⁻¹V, 𝒪)` for every quasi-compact
quasi-separated open `V ⊆ T`. -/
theorem isIso_app_pullback_snd_of_isIso_appTop {S X T : Scheme.{u}} [IsAffine S] (f : X ⟶ S)
    (g : T ⟶ S) [Flat g] [CompactSpace X] [QuasiSeparatedSpace X] [IsIso f.appTop]
    (V : T.Opens) (hV : IsCompact (V : Set T)) (hV' : IsQuasiSeparated (V : Set T)) :
    IsIso ((pullback.snd f g).app V) := by
  have H := IsPullback.of_hasPullback f g
  have hUY : (pullback.snd f g) ⁻¹ᵁ V = (pullback.fst f g) ⁻¹ᵁ ⊤ ⊓ (pullback.snd f g) ⁻¹ᵁ V := by
    simp
  have e : f.appLE ⊤ ⊤ le_top = f.appTop := Scheme.Hom.appLE_eq_app f
  have hfl : (f.appLE ⊤ ⊤ le_top).hom.Flat := by
    rw [e]
    exact RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso f.appTop)
  have hiso := isIso_pushoutSection_of_isCompact_of_flat_right_of_ringHomFlat H
    (US := ⊤) (UX := ⊤) (le_top : V ≤ g ⁻¹ᵁ ⊤) (le_top : (⊤ : X.Opens) ≤ f ⁻¹ᵁ ⊤) hUY
    (isAffineOpen_top S) hV hV'
    (by simpa using isCompact_univ) (by simpa using isQuasiSeparated_univ) hfl
  have hpo := (isIso_pushoutSection_iff H _ _ hUY).mp hiso
  have : IsIso (f.appLE ⊤ ⊤ le_top) := by
    rw [e]
    infer_instance
  have h := hpo.isIso_inr_of_isIso
  have e' : (pullback.snd f g).appLE V ((pullback.snd f g) ⁻¹ᵁ V) le_rfl =
      (pullback.snd f g).app V := Scheme.Hom.appLE_eq_app _
  rwa [e'] at h

/-- **`𝒪_T ⟶ p_*𝒪_{X ×_S T}` is an isomorphism** for `S` affine, `f : X ⟶ S` qcqs with
`Γ(S, 𝒪) ≅ Γ(X, 𝒪)` and `g : T ⟶ S` flat: it is so on every affine open of `T`
(`isIso_app_pullback_snd_of_isIso_appTop`), and the affine opens form a basis. -/
theorem isIso_structureSheafHom_pullback_snd_of_isIso_appTop {S X T : Scheme.{u}} [IsAffine S]
    (f : X ⟶ S) (g : T ⟶ S) [Flat g] [CompactSpace X] [QuasiSeparatedSpace X]
    [IsIso f.appTop] :
    IsIso (RingedSpaceModuleAdjunction.structureSheafHom
      (pullback.snd f g).toLRSHom.toShHom) := by
  let p := pullback.snd f g
  have hB : Opens.IsBasis (Set.range (fun i : T.affineOpens => (i : T.Opens))) := by
    rw [Subtype.range_coe]
    exact T.isBasis_affineOpens
  let ψ : T.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat p.base).obj (pullback f g).sheaf :=
    ⟨p.c⟩
  have hψ : IsIso ψ := TopCat.Sheaf.isIso_iff_isIso_basis hB (fun i => by
    show IsIso (p.app i.1)
    exact isIso_app_pullback_snd_of_isIso_appTop f g i.1 i.2.isCompact i.2.isQuasiSeparated)
  rw [← isIso_iff_of_reflects_iso _ (sheafToPresheaf _ _)]
  show IsIso (Functor.whiskerRight p.toLRSHom.toHom.c (forget₂ CommRingCat RingCat))
  have : IsIso p.toLRSHom.toHom.c := inferInstanceAs (IsIso ((TopCat.Sheaf.forget _ _).map ψ))
  infer_instance

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A]

/-- **`Γ(A × A, 𝒪) = k`** for an abelian variety `A` over `k`: `Γ(A, 𝒪) = k`
([Stacks, Tag 0BUG]) and flat base change (`isIso_app_pullback_snd_of_isIso_appTop` at the
top open). -/
theorem isIso_appTop_tensorObj_hom [AlgebraicGeometry.IsAbelianVariety k A] :
    IsIso (A ⊗ A).hom.appTop := by
  have hA : IsIso A.hom.appTop := by
    have h := isIso_globalSections_of_geometricallyIntegral k A.hom
    exact IsIso.of_isIso_comp_left (Scheme.ΓSpecIso (.of k)).inv A.hom.appTop
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  have : QuasiSeparatedSpace A.left := quasiSeparatedSpace_of_quasiSeparated A.hom
  show IsIso (pullback.fst A.hom A.hom ≫ A.hom).appTop
  rw [pullback.condition, Scheme.Hom.comp_appTop]
  have : IsIso (pullback.snd A.hom A.hom).appTop :=
    isIso_app_pullback_snd_of_isIso_appTop A.hom A.hom ⊤
      (by simpa using isCompact_univ) (by simpa using isQuasiSeparated_univ)
  infer_instance

/-- **`𝒪_A ⟶ p_*𝒪_{A × A × A}` is an isomorphism** for the third projection
`p : A × A × A ⟶ A` of an abelian variety. -/
theorem isIso_structureSheafHom_cubeProj₃ [AlgebraicGeometry.IsAbelianVariety k A] :
    IsIso (RingedSpaceModuleAdjunction.structureSheafHom
      (cubeProj₃ A).left.toLRSHom.toShHom) := by
  have := isIso_appTop_tensorObj_hom A
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  have : CompactSpace (A ⊗ A).left := inferInstanceAs (CompactSpace ↥(pullback A.hom A.hom))
  have : QuasiSeparatedSpace (A ⊗ A).left :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.fst A.hom A.hom ≫ A.hom)
  exact isIso_structureSheafHom_pullback_snd_of_isIso_appTop (A ⊗ A).hom A.hom

end Stacks.Groupoids

end
