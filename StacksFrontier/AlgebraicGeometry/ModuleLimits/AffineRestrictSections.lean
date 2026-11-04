module

public import StacksFrontier.AlgebraicGeometry.ModuleLimits.AffineHom
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.RestrictSections

/-!
# A morphism over an affine open is a linear map on the sections over it

Let `X` be a scheme, let `M` and `N` be quasi-coherent `𝒪_X`-modules and let `O` be an
**affine** open of `X`.  This file proves that a morphism `M|_O ⟶ N|_O` is the same datum as a
`Γ(X, O)`-linear map `Γ(M, O) → Γ(N, O)`: the comparison
`Stacks.AlgebraicGeometry.ModuleLimits.restrictSections`, which reads a morphism of the
restrictions on the sections over each open `U ≤ O`, is injective and its value at `U = O` may
be prescribed arbitrarily. This is the comparison
`Hom_{𝒪_O}(M|_O, N|_O) ≅ Hom_{Γ(X,O)}(Γ(M, O), Γ(N, O))`.

## Main definitions

* `Stacks.AlgebraicGeometry.ModuleLimits.restrictTopLinearMap`: a `Γ(X, O)`-linear map on the
  sections over `O`, read as a linear map on the global sections of the restrictions to the open
  subscheme `O`.

## Main results

* `Stacks.AlgebraicGeometry.ModuleLimits.exists_restrictSections_eq_of_isAffineOpen`:
  **fullness.** Every `Γ(X, O)`-linear map `Γ(M, O) → Γ(N, O)` is the value at `O` of the
  sectionwise family of a morphism `M|_O ⟶ N|_O`.
* `Stacks.AlgebraicGeometry.ModuleLimits.restrictSections_ext_of_isAffineOpen`:
  **faithfulness.** Two morphisms `M|_O ⟶ N|_O` whose sectionwise families agree at `O` are
  equal.
* `Stacks.AlgebraicGeometry.ModuleLimits.exists_sectionFamily_of_isAffineOpen` and
  `Stacks.AlgebraicGeometry.ModuleLimits.sectionFamily_ext_of_isAffineOpen`: the same two
  statements with the morphism replaced by a family of maps `Γ(M, U) → Γ(N, U)`, one for each
  open `U ≤ O`, additive, `Γ(X, U)`-homogeneous and compatible with restriction. Such a family
  exists with any prescribed value at `O`, and is determined by that value.

## Implementation notes

The affine input is `Stacks.AlgebraicGeometry.ModuleLimits.exists_hom_app_top_eq` and
`Stacks.AlgebraicGeometry.ModuleLimits.hom_ext_of_app_top`, the fullness and faithfulness of
global sections on an affine scheme, applied to the affine scheme `O` and to the restrictions
`M|_O` and `N|_O`, which are quasi-coherent. The global sections of `M|_O` are the sections of
`M` over `O.ι ''ᵁ ⊤`, which is `O` only up to `AlgebraicGeometry.Scheme.Opens.ι_image_top`. No
`eqToHom` is needed to pass between the two: both inclusions between `O` and `O.ι ''ᵁ ⊤` exist,
so the two restriction maps of the presheaf along them are mutually inverse by
`Stacks.AlgebraicGeometry.ModuleLimits.modules_presheaf_map_homOfLE_self`.

The map `restrictTopLinearMap` is defined through
`AlgebraicGeometry.Scheme.Modules.restrictAppIso`; its homogeneity compares the scalar actions
of `Γ(O, ⊤)` and of `Γ(X, O.ι ''ᵁ ⊤)` through `AlgebraicGeometry.Scheme.Opens.ι_appIso`.

## References

* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules

universe u

namespace Stacks.AlgebraicGeometry.ModuleLimits

variable {X : Scheme.{u}} {M N : X.Modules}

/-! ### A linear map on the sections over an open, read on the open subscheme -/

/-- A `Γ(X, O)`-linear map on the sections of `M` and `N` over `O`, read as a linear map on the
global sections of the restrictions of `M` and `N` to the open subscheme `O`.  The two
hom-modules have different scalars — `Γ(X, O)` on one side and `Γ(O, ⊤) = Γ(X, O.ι ''ᵁ ⊤)` on
the other — so the map is conjugated by the restriction maps between `O` and `O.ι ''ᵁ ⊤`. -/
noncomputable def restrictTopLinearMap (O : X.Opens) (f : Γ(M, O) →ₗ[Γ(X, O)] Γ(N, O)) :
    Γ(Scheme.Modules.restrict M O.ι, ⊤) →ₗ[Γ(O.toScheme, ⊤)]
      Γ(Scheme.Modules.restrict N O.ι, ⊤) where
  toFun x := (Scheme.Modules.restrictAppIso O.ι N ⊤).inv
    (N.presheaf.map (homOfLE O.ι_image_top.le).op
      (f (M.presheaf.map (homOfLE O.ι_image_top.ge).op
        ((Scheme.Modules.restrictAppIso O.ι M ⊤).hom x))))
  map_add' x y := by
    simp only [map_add]
  map_smul' r x := by
    simp only [RingHom.id_apply]
    rw [smul_restrictAppIso_hom_apply, Scheme.Modules.map_smul, LinearMap.map_smul,
      Scheme.Modules.map_smul, structure_presheaf_map_homOfLE_self,
      smul_restrictAppIso_inv_apply, CommRingCat.hom_inv_apply]

/-- The value of `restrictTopLinearMap O f` at a global section `x` of `M|_O`: transport `x` to
`Γ(M, O)`, apply `f`, and transport back. -/
theorem restrictTopLinearMap_apply (O : X.Opens) (f : Γ(M, O) →ₗ[Γ(X, O)] Γ(N, O))
    (x : Γ(Scheme.Modules.restrict M O.ι, ⊤)) :
    restrictTopLinearMap O f x = (Scheme.Modules.restrictAppIso O.ι N ⊤).inv
      (N.presheaf.map (homOfLE O.ι_image_top.le).op
        (f (M.presheaf.map (homOfLE O.ι_image_top.ge).op
          ((Scheme.Modules.restrictAppIso O.ι M ⊤).hom x)))) := rfl

/-! ### The sectionwise family at the open itself -/

/-- The value at `O` of the sectionwise family of a morphism of the restrictions to `O`, in
terms of its action on global sections. -/
theorem restrictSections_self (O : X.Opens)
    (θ : Scheme.Modules.restrict M O.ι ⟶ Scheme.Modules.restrict N O.ι) (m : Γ(M, O)) :
    restrictSections θ O le_rfl m
      = N.presheaf.map (homOfLE O.ι_image_top.ge).op
          ((Scheme.Modules.restrictAppIso O.ι N ⊤).hom
            (θ.app ⊤ ((Scheme.Modules.restrictAppIso O.ι M ⊤).inv
              (M.presheaf.map (homOfLE O.ι_image_top.le).op m)))) := by
  have h := restrictSections_res θ O (O.ι ''ᵁ ⊤) O.ι_image_top.ge O.ι_image_top.le
    (M.presheaf.map (homOfLE O.ι_image_top.le).op m)
  rw [modules_presheaf_map_homOfLE_self O.ι_image_top.le O.ι_image_top.ge m] at h
  rw [h, restrictSections_image θ ⊤ O.ι_image_top.le]
  unfold restrictHomApp
  simp only [ConcreteCategory.comp_apply]

/-! ### Fullness and faithfulness over an affine open -/

/-- **Fullness over an affine open.** Every `Γ(X, O)`-linear map `Γ(M, O) → Γ(N, O)` between
the sections of two quasi-coherent modules over an affine open is the value at `O` of the
sectionwise family of a morphism `M|_O ⟶ N|_O`. -/
theorem exists_restrictSections_eq_of_isAffineOpen [M.IsQuasicoherent] [N.IsQuasicoherent]
    {O : X.Opens} (hO : IsAffineOpen O) (f : Γ(M, O) →ₗ[Γ(X, O)] Γ(N, O)) :
    ∃ θ : Scheme.Modules.restrict M O.ι ⟶ Scheme.Modules.restrict N O.ι,
      ∀ m : Γ(M, O), restrictSections θ O le_rfl m = f m := by
  have : IsAffine O.toScheme := hO
  obtain ⟨θ, hθ⟩ := exists_hom_app_top_eq (X := O.toScheme)
    (F := Scheme.Modules.restrict M O.ι) (G := Scheme.Modules.restrict N O.ι)
    (restrictTopLinearMap O f)
  refine ⟨θ, fun m => ?_⟩
  rw [restrictSections_self, hθ, restrictTopLinearMap_apply]
  simp only [Iso.inv_hom_id_apply, modules_presheaf_map_homOfLE_self]

/-- Two morphisms `M|_O ⟶ N|_O` whose sectionwise families agree at `O` agree on global
sections. -/
theorem app_top_eq_of_restrictSections_self {O : X.Opens}
    {θ θ' : Scheme.Modules.restrict M O.ι ⟶ Scheme.Modules.restrict N O.ι}
    (h : ∀ m : Γ(M, O), restrictSections θ O le_rfl m = restrictSections θ' O le_rfl m)
    (a : Γ(Scheme.Modules.restrict M O.ι, ⊤)) : θ.app ⊤ a = θ'.app ⊤ a := by
  have ha := h (M.presheaf.map (homOfLE O.ι_image_top.ge).op
    ((Scheme.Modules.restrictAppIso O.ι M ⊤).hom a))
  rw [restrictSections_self, restrictSections_self] at ha
  simp only [modules_presheaf_map_homOfLE_self, Iso.hom_inv_id_apply] at ha
  have hb := congrArg (N.presheaf.map (homOfLE O.ι_image_top.le).op) ha
  simp only [modules_presheaf_map_homOfLE_self] at hb
  exact (ConcreteCategory.bijective_of_isIso
    (Scheme.Modules.restrictAppIso O.ι N ⊤).hom).injective hb

/-- **Faithfulness over an affine open.** Two morphisms `M|_O ⟶ N|_O` between the restrictions
of two quasi-coherent modules to an affine open whose sectionwise families agree at `O` are
equal. -/
theorem restrictSections_ext_of_isAffineOpen [M.IsQuasicoherent] [N.IsQuasicoherent]
    {O : X.Opens} (hO : IsAffineOpen O)
    {θ θ' : Scheme.Modules.restrict M O.ι ⟶ Scheme.Modules.restrict N O.ι}
    (h : ∀ m : Γ(M, O), restrictSections θ O le_rfl m = restrictSections θ' O le_rfl m) :
    θ = θ' :=
  let : IsAffine O.toScheme := hO
  hom_ext_of_app_top (X := O.toScheme) (app_top_eq_of_restrictSections_self h)

/-! ### The sectionwise form -/

/-- **Fullness over an affine open, sectionwise.** Every `Γ(X, O)`-linear map
`Γ(M, O) → Γ(N, O)` extends to a family of maps on the sections over the opens contained in the
affine open `O`, additive, homogeneous and compatible with restriction. -/
theorem exists_sectionFamily_of_isAffineOpen [M.IsQuasicoherent] [N.IsQuasicoherent]
    {O : X.Opens} (hO : IsAffineOpen O) (f : Γ(M, O) →ₗ[Γ(X, O)] Γ(N, O)) :
    ∃ t : ∀ U : X.Opens, U ≤ O → Γ(M, U) → Γ(N, U),
      (∀ (U : X.Opens) (h : U ≤ O) (m m' : Γ(M, U)), t U h (m + m') = t U h m + t U h m') ∧
      (∀ (U : X.Opens) (h : U ≤ O) (r : Γ(X, U)) (m : Γ(M, U)), t U h (r • m) = r • t U h m) ∧
      (∀ (U V : X.Opens) (hUV : U ≤ V) (hV : V ≤ O) (m : Γ(M, V)),
        t U (hUV.trans hV) (M.presheaf.map (homOfLE hUV).op m)
          = N.presheaf.map (homOfLE hUV).op (t V hV m)) ∧
      ∀ m : Γ(M, O), t O le_rfl m = f m := by
  obtain ⟨θ, hθ⟩ := exists_restrictSections_eq_of_isAffineOpen (M := M) (N := N) hO f
  exact ⟨restrictSections θ, restrictSections_add θ, restrictSections_smul θ,
    restrictSections_res θ, hθ⟩

/-- **Faithfulness over an affine open, sectionwise.** A family of maps on the sections over the
opens contained in an affine open `O` which is additive, homogeneous and compatible with
restriction is determined by its value at `O`. -/
theorem sectionFamily_ext_of_isAffineOpen [M.IsQuasicoherent] [N.IsQuasicoherent]
    {O : X.Opens} (hO : IsAffineOpen O)
    (t t' : ∀ U : X.Opens, U ≤ O → Γ(M, U) → Γ(N, U))
    (hadd : ∀ (U : X.Opens) (h : U ≤ O) (m m' : Γ(M, U)), t U h (m + m') = t U h m + t U h m')
    (hsmul : ∀ (U : X.Opens) (h : U ≤ O) (r : Γ(X, U)) (m : Γ(M, U)), t U h (r • m) = r • t U h m)
    (hres : ∀ (U V : X.Opens) (hUV : U ≤ V) (hV : V ≤ O) (m : Γ(M, V)),
      t U (hUV.trans hV) (M.presheaf.map (homOfLE hUV).op m)
        = N.presheaf.map (homOfLE hUV).op (t V hV m))
    (hadd' : ∀ (U : X.Opens) (h : U ≤ O) (m m' : Γ(M, U)),
      t' U h (m + m') = t' U h m + t' U h m')
    (hsmul' : ∀ (U : X.Opens) (h : U ≤ O) (r : Γ(X, U)) (m : Γ(M, U)),
      t' U h (r • m) = r • t' U h m)
    (hres' : ∀ (U V : X.Opens) (hUV : U ≤ V) (hV : V ≤ O) (m : Γ(M, V)),
      t' U (hUV.trans hV) (M.presheaf.map (homOfLE hUV).op m)
        = N.presheaf.map (homOfLE hUV).op (t' V hV m))
    (h : ∀ m : Γ(M, O), t O le_rfl m = t' O le_rfl m) :
    ∀ (U : X.Opens) (hU : U ≤ O) (m : Γ(M, U)), t U hU m = t' U hU m := by
  have hEq : homOfRestrictSections (M := M) (N := N) O t hadd hsmul hres
      = homOfRestrictSections O t' hadd' hsmul' hres' := by
    refine restrictSections_ext_of_isAffineOpen hO fun m => ?_
    simpa only [restrictSections_homOfRestrictSections] using h m
  intro U hU m
  rw [← restrictSections_homOfRestrictSections O t hadd hsmul hres U hU m,
    ← restrictSections_homOfRestrictSections O t' hadd' hsmul' hres' U hU m, hEq]

end Stacks.AlgebraicGeometry.ModuleLimits

end
