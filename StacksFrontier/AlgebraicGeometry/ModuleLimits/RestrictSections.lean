module

public import StacksFrontier.AlgebraicGeometry.ModuleLimits.HomGlue

/-!
# Morphisms between the restrictions to an open, and their action on sections

A morphism `θ : M|_O ⟶ N|_O` between the restrictions of two sheaves of modules to an open `O`
of a scheme carries the same information as its *action on sections*: a family of maps
`Γ(M, U) → Γ(N, U)`, one for every open `U ≤ O`, which is additive, `Γ(X, U)`-homogeneous and
compatible with restriction along inclusions of opens.  This file sets up that dictionary.

It is what a Zariski-glueing argument for [Stacks Project, Tag 01ZR] (2) needs: the glueing
tool `Stacks.AlgebraicGeometry.ModuleLimits.exists_hom_app_eq_of_cover` consumes *sectionwise*
data, whereas the descent of a morphism over one member of an affine covering produces a
*morphism of restrictions*, and the two presentations are related by exactly the transport
proved here.

## Main definitions

* `Stacks.AlgebraicGeometry.ModuleLimits.restrictHomApp`: the action of `θ` on the sections over
  the image `O.ι ''ᵁ U'` of an open of `O`, written in the ambient scheme's spelling.
* `Stacks.AlgebraicGeometry.ModuleLimits.restrictSections`: the action of `θ` on the sections
  over an open `U` of the ambient scheme contained in `O`.
* `Stacks.AlgebraicGeometry.ModuleLimits.homOfRestrictSections`: the morphism of restrictions
  attached to a sectionwise family; inverse to `restrictSections`.
* `Stacks.AlgebraicGeometry.ModuleLimits.restrictTo`: the restriction of a morphism of
  restrictions to a smaller open.

## Main results

* `Stacks.AlgebraicGeometry.ModuleLimits.restrictSections_add`,
  `restrictSections_smul`, `restrictSections_res`: the sectionwise family of a morphism of
  restrictions is additive, homogeneous and compatible with restriction, which is exactly the
  data the glueing tool asks for.
* `Stacks.AlgebraicGeometry.ModuleLimits.restrictSections_homOfRestrictSections` and
  `Stacks.AlgebraicGeometry.ModuleLimits.restrictSections_ext`: the two constructions are
  mutually inverse.
* `Stacks.AlgebraicGeometry.ModuleLimits.restrictSections_restrictFunctor_map`: the sectionwise
  family of the restriction of a morphism defined on all of `X` is that morphism's own action on
  sections.

## Implementation notes

For `U ≤ O` the open `O.ι ''ᵁ (O.ι ⁻¹ᵁ U)` is *equal* to `U` but not definitionally so, which is
why `restrictSections` cannot be `θ.app (O.ι ⁻¹ᵁ U)` on the nose.  No `eqToHom` and no cast is
needed to repair this: the two inclusions between `U` and `O.ι ''ᵁ (O.ι ⁻¹ᵁ U)` both exist, so
the two restriction maps of the presheaf along them are available, and
`modules_presheaf_map_homOfLE_self` says they are mutually inverse.  `restrictSections` is the
middle one conjugated by that pair.

The second shape point is that the sections of `M.restrict O.ι` over `U'` are the sections of
`M` over `O.ι ''ᵁ U'` only up to an unfolding that is **not** available at reducible
transparency, so a `rw` on a goal that mixes the two spellings fails with
`Application type mismatch` — Mathlib provides
`AlgebraicGeometry.Scheme.Modules.restrictAppIso`, the identity isomorphism between them, for
exactly this reason, and every statement here is written on the ambient side of it.  Writing a
section type as `Γ(M.restrict O.ι, U')` instead is not merely inconvenient: unifying it against
`Γ(M, ?U)` exhausts the heartbeat budget, where the same step in the `Γ(M, O.ι ''ᵁ U')` spelling
costs four thousand heartbeats.

## References

* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules

universe u

namespace Stacks.AlgebraicGeometry.ModuleLimits

section

variable {Y : TopCat.{u}} {C : Type*} [Category C]

/-- Restricting along two mutually inverse inclusions of opens is the identity. -/
theorem presheaf_map_homOfLE_comp_self (P : TopCat.Presheaf C Y) {U V : Opens Y}
    (h₁ : V ≤ U) (h₂ : U ≤ V) :
    P.map (homOfLE h₁).op ≫ P.map (homOfLE h₂).op = 𝟙 (P.obj (op U)) := by
  rw [← P.map_comp,
    show ((homOfLE h₁).op ≫ (homOfLE h₂).op) = 𝟙 (op U) from Subsingleton.elim _ _]
  exact P.map_id _

end

section

variable {X : Scheme.{u}} {M N : X.Modules}

/-- Restricting a section along two mutually inverse inclusions of opens does nothing. -/
theorem modules_presheaf_map_homOfLE_self {U V : X.Opens} (h₁ : V ≤ U) (h₂ : U ≤ V) (m : Γ(M, U)) :
    M.presheaf.map (homOfLE h₂).op (M.presheaf.map (homOfLE h₁).op m) = m := by
  rw [← ConcreteCategory.comp_apply, presheaf_map_homOfLE_comp_self]
  simp

/-- Restricting a section along two mutually inverse inclusions of opens does nothing, in the
`· .val.map` spelling. -/
theorem val_map_homOfLE_self {U V : X.Opens} (h₁ : V ≤ U) (h₂ : U ≤ V)
    (m : M.val.obj (op U)) :
    M.val.map (homOfLE h₂).op (M.val.map (homOfLE h₁).op m) = m := by
  rw [← PresheafOfModules.map_comp_apply,
    PresheafOfModules.congr_map_apply M.val
      (Subsingleton.elim ((homOfLE h₁).op ≫ (homOfLE h₂).op) (𝟙 (op U))) m]
  simp
  rfl

/-- Restricting a function along two mutually inverse inclusions of opens does nothing. -/
theorem structure_presheaf_map_homOfLE_self {U V : X.Opens} (h₁ : V ≤ U) (h₂ : U ≤ V)
    (r : Γ(X, U)) : X.presheaf.map (homOfLE h₂).op (X.presheaf.map (homOfLE h₁).op r) = r := by
  rw [← ConcreteCategory.comp_apply, presheaf_map_homOfLE_comp_self]
  simp

/-! ### The action on sections of a morphism of restrictions -/

/-- The action on sections of a morphism between the restrictions of `M` and `N` to an open
`O`, written in the ambient scheme's spelling: the sections of `M.restrict O.ι` over an open
`U'` of `O` are the sections of `M` over `O.ι ''ᵁ U'`. -/
noncomputable def restrictHomApp {O : X.Opens}
    (θ : Scheme.Modules.restrict M O.ι ⟶ Scheme.Modules.restrict N O.ι)
    (U' : O.toScheme.Opens) : Γ(M, O.ι ''ᵁ U') ⟶ Γ(N, O.ι ''ᵁ U') :=
  (Scheme.Modules.restrictAppIso O.ι M U').inv ≫ θ.app U' ≫
    (Scheme.Modules.restrictAppIso O.ι N U').hom

/-- `restrictHomApp` in the `· .val.app (op U')` spelling, which is the spelling the
`AlgebraicGeometry.Scheme.Modules.pullbackSection` lemmas are stated in.  This is the one
crossing between the two spellings; every statement here is on the ambient side of it. -/
theorem restrictHomApp_apply {O : X.Opens}
    (θ : Scheme.Modules.restrict M O.ι ⟶ Scheme.Modules.restrict N O.ι)
    (U' : O.toScheme.Opens) (m : Γ(M, O.ι ''ᵁ U')) :
    restrictHomApp θ U' m = θ.val.app (op U') m := by
  unfold restrictHomApp
  simp only [ConcreteCategory.comp_apply]
  rfl

/-- `restrictHomApp` commutes with restriction of sections along an inclusion of opens of `O`. -/
theorem restrictHomApp_naturality {O : X.Opens}
    (θ : Scheme.Modules.restrict M O.ι ⟶ Scheme.Modules.restrict N O.ι)
    {U' V' : O.toScheme.Opens} (h : U' ≤ V') (m : Γ(M, O.ι ''ᵁ V')) :
    N.presheaf.map (homOfLE (Scheme.Hom.image_mono O.ι h)).op (restrictHomApp θ V' m)
      = restrictHomApp θ U' (M.presheaf.map (homOfLE (Scheme.Hom.image_mono O.ι h)).op m) := by
  unfold restrictHomApp
  simp only [ConcreteCategory.comp_apply]
  rw [← map_restrictAppIso_hom_apply O.ι N (homOfLE h).op, Hom_app_presheaf_map θ h,
    ← restrictAppIso_inv_map_apply O.ι M (homOfLE h).op]

/-- `restrictHomApp` is `Γ(X, O.ι ''ᵁ U')`-homogeneous. -/
theorem restrictHomApp_smul {O : X.Opens}
    (θ : Scheme.Modules.restrict M O.ι ⟶ Scheme.Modules.restrict N O.ι)
    (U' : O.toScheme.Opens) (r : Γ(X, O.ι ''ᵁ U')) (m : Γ(M, O.ι ''ᵁ U')) :
    restrictHomApp θ U' (r • m) = r • restrictHomApp θ U' m := by
  unfold restrictHomApp
  simp only [ConcreteCategory.comp_apply]
  rw [smul_restrictAppIso_inv_apply, Scheme.Modules.Hom.app_smul,
    smul_restrictAppIso_hom_apply, CommRingCat.inv_hom_apply]

/-- A morphism of restrictions to `O` is determined by its action `restrictHomApp` on sections. -/
theorem restrictHom_ext {O : X.Opens}
    {θ θ' : Scheme.Modules.restrict M O.ι ⟶ Scheme.Modules.restrict N O.ι}
    (h : ∀ (U' : O.toScheme.Opens) (m : Γ(M, O.ι ''ᵁ U')),
      restrictHomApp θ U' m = restrictHomApp θ' U' m) : θ = θ' := by
  refine Scheme.Modules.hom_ext _ _ fun U' => ?_
  ext x
  have hx := h U' ((Scheme.Modules.restrictAppIso O.ι M U').hom x)
  unfold restrictHomApp at hx
  simp only [ConcreteCategory.comp_apply, AddCommGrpCat.neg_hom_apply] at hx
  have hx' := congrArg (fun y => (Scheme.Modules.restrictAppIso O.ι N U').inv y) hx
  simpa only [AddCommGrpCat.neg_hom_apply] using hx'

/-! ### The sectionwise family of a morphism of restrictions -/

/-- The action on sections of a morphism of the restrictions to `O`, indexed by the opens of
the ambient scheme contained in `O`. -/
noncomputable def restrictSections {O : X.Opens}
    (θ : Scheme.Modules.restrict M O.ι ⟶ Scheme.Modules.restrict N O.ι)
    (U : X.Opens) (h : U ≤ O) (m : Γ(M, U)) : Γ(N, U) :=
  N.presheaf.map (homOfLE (image_preimage_of_le h).ge).op
    (restrictHomApp θ (O.ι ⁻¹ᵁ U) (M.presheaf.map (homOfLE (O.ι.image_preimage_le U)).op m))

/-- `restrictSections` in the `· .val.app (op U')` spelling. -/
theorem restrictSections_apply {O : X.Opens}
    (θ : Scheme.Modules.restrict M O.ι ⟶ Scheme.Modules.restrict N O.ι)
    (U : X.Opens) (h : U ≤ O) (m : Γ(M, U)) :
    restrictSections θ U h m
      = N.val.map (homOfLE (image_preimage_of_le h).ge).op
          (θ.val.app (op (O.ι ⁻¹ᵁ U)) (M.val.map (homOfLE (O.ι.image_preimage_le U)).op m)) := by
  unfold restrictSections
  rw [restrictHomApp_apply]
  rfl

/-- The sectionwise family of a morphism of restrictions is additive. -/
theorem restrictSections_add {O : X.Opens}
    (θ : Scheme.Modules.restrict M O.ι ⟶ Scheme.Modules.restrict N O.ι)
    (U : X.Opens) (h : U ≤ O) (m m' : Γ(M, U)) :
    restrictSections θ U h (m + m') = restrictSections θ U h m + restrictSections θ U h m' := by
  unfold restrictSections
  rw [map_add, map_add, map_add]

/-- The sectionwise family of a morphism of restrictions is `Γ(X, U)`-homogeneous. -/
theorem restrictSections_smul {O : X.Opens}
    (θ : Scheme.Modules.restrict M O.ι ⟶ Scheme.Modules.restrict N O.ι)
    (U : X.Opens) (h : U ≤ O) (r : Γ(X, U)) (m : Γ(M, U)) :
    restrictSections θ U h (r • m) = r • restrictSections θ U h m := by
  unfold restrictSections
  rw [Scheme.Modules.map_smul, restrictHomApp_smul, Scheme.Modules.map_smul,
    structure_presheaf_map_homOfLE_self]

/-- The sectionwise family of a morphism of restrictions commutes with restriction of sections
along an inclusion of opens contained in `O`. -/
theorem restrictSections_res {O : X.Opens}
    (θ : Scheme.Modules.restrict M O.ι ⟶ Scheme.Modules.restrict N O.ι)
    (U V : X.Opens) (hUV : U ≤ V) (hV : V ≤ O) (m : Γ(M, V)) :
    restrictSections θ U (hUV.trans hV) (M.presheaf.map (homOfLE hUV).op m)
      = N.presheaf.map (homOfLE hUV).op (restrictSections θ V hV m) := by
  unfold restrictSections
  have hp : O.ι ⁻¹ᵁ U ≤ O.ι ⁻¹ᵁ V := Scheme.Hom.preimage_mono _ hUV
  rw [presheaf_map_homOfLE_comp,
    ← presheaf_map_homOfLE_comp (h₁ := O.ι.image_preimage_le V)
      (h₂ := Scheme.Hom.image_mono O.ι hp),
    ← restrictHomApp_naturality θ hp, presheaf_map_homOfLE_comp, presheaf_map_homOfLE_comp]

/-- On the image of an open of `O`, the sectionwise family is the morphism's own action. -/
theorem restrictSections_image {O : X.Opens}
    (θ : Scheme.Modules.restrict M O.ι ⟶ Scheme.Modules.restrict N O.ι)
    (U' : O.toScheme.Opens) (h : O.ι ''ᵁ U' ≤ O) (m : Γ(M, O.ι ''ᵁ U')) :
    restrictSections θ (O.ι ''ᵁ U') h m = restrictHomApp θ U' m := by
  unfold restrictSections
  have hle : O.ι ⁻¹ᵁ (O.ι ''ᵁ U') ≤ U' := (O.ι.preimage_image_eq U').le
  rw [show (homOfLE (O.ι.image_preimage_le (O.ι ''ᵁ U')))
      = homOfLE (Scheme.Hom.image_mono O.ι hle) from Subsingleton.elim _ _,
    ← restrictHomApp_naturality θ hle m, modules_presheaf_map_homOfLE_self]

/-- A morphism of restrictions to `O` is determined by its sectionwise family. -/
theorem restrictSections_ext {O : X.Opens}
    {θ θ' : Scheme.Modules.restrict M O.ι ⟶ Scheme.Modules.restrict N O.ι}
    (h : ∀ (U : X.Opens) (hU : U ≤ O) (m : Γ(M, U)),
      restrictSections θ U hU m = restrictSections θ' U hU m) : θ = θ' := by
  refine restrictHom_ext fun U' m => ?_
  rw [← restrictSections_image θ U' (Scheme.Opens.ι_image_le O U') m,
    ← restrictSections_image θ' U' (Scheme.Opens.ι_image_le O U') m]
  exact h _ _ m

/-! ### A morphism of restrictions from a sectionwise family -/

/-- A morphism between the restrictions to `O` from its action on sections. -/
noncomputable def homOfRestrictSections (O : X.Opens)
    (t : ∀ (U : X.Opens), U ≤ O → Γ(M, U) → Γ(N, U))
    (hadd : ∀ (U : X.Opens) (h : U ≤ O) (m m' : Γ(M, U)),
      t U h (m + m') = t U h m + t U h m')
    (hsmul : ∀ (U : X.Opens) (h : U ≤ O) (r : Γ(X, U)) (m : Γ(M, U)),
      t U h (r • m) = r • t U h m)
    (hres : ∀ (U V : X.Opens) (hUV : U ≤ V) (hV : V ≤ O) (m : Γ(M, V)),
      t U (hUV.trans hV) (M.presheaf.map (homOfLE hUV).op m)
        = N.presheaf.map (homOfLE hUV).op (t V hV m)) :
    Scheme.Modules.restrict M O.ι ⟶ Scheme.Modules.restrict N O.ι :=
  homOfSections
    (fun U' => fun x => (Scheme.Modules.restrictAppIso O.ι N U').inv
      (t (O.ι ''ᵁ U') (Scheme.Opens.ι_image_le O U')
        ((Scheme.Modules.restrictAppIso O.ι M U').hom x)))
    (fun U' x y => by
      rw [map_add, hadd, map_add])
    (fun U' r x => by
      rw [smul_restrictAppIso_hom_apply, hsmul, smul_restrictAppIso_inv_apply,
        CommRingCat.hom_inv_apply])
    (fun U' V' hle x => by
      rw [restrictAppIso_inv_map_apply O.ι N (homOfLE hle).op,
        map_restrictAppIso_hom_apply O.ι M (homOfLE hle).op,
        hres (O.ι ''ᵁ U') (O.ι ''ᵁ V') (Scheme.Hom.image_mono O.ι hle)
          (Scheme.Opens.ι_image_le O V')])

/-- The action on sections of `homOfRestrictSections` over the image of an open of `O` is the
family it was built from. -/
theorem restrictHomApp_homOfRestrictSections (O : X.Opens) (t) (hadd) (hsmul) (hres)
    (U' : O.toScheme.Opens) (m : Γ(M, O.ι ''ᵁ U')) :
    restrictHomApp (M := M) (N := N) (homOfRestrictSections O t hadd hsmul hres) U' m
      = t (O.ι ''ᵁ U') (Scheme.Opens.ι_image_le O U') m := by
  unfold restrictHomApp homOfRestrictSections
  simp only [ConcreteCategory.comp_apply, homOfSections_app]
  rw [AddCommGrpCat.hom_neg_apply, AddCommGrpCat.hom_neg_apply]

/-- The sectionwise family of `homOfRestrictSections` is the family it was built from. -/
theorem restrictSections_homOfRestrictSections (O : X.Opens) (t) (hadd) (hsmul) (hres)
    (U : X.Opens) (h : U ≤ O) (m : Γ(M, U)) :
    restrictSections (M := M) (N := N) (homOfRestrictSections O t hadd hsmul hres) U h m
      = t U h m := by
  unfold restrictSections
  rw [restrictHomApp_homOfRestrictSections, hres _ _ (O.ι.image_preimage_le U) h m,
    modules_presheaf_map_homOfLE_self]

/-! ### Restriction to a smaller open, and the restriction of a global morphism -/

/-- The restriction of a morphism of restrictions to a smaller open. -/
noncomputable def restrictTo {O O' : X.Opens} (hO : O' ≤ O)
    (θ : Scheme.Modules.restrict M O.ι ⟶ Scheme.Modules.restrict N O.ι) :
    Scheme.Modules.restrict M O'.ι ⟶ Scheme.Modules.restrict N O'.ι :=
  homOfRestrictSections O' (fun U h => restrictSections θ U (h.trans hO))
    (fun U h => restrictSections_add θ U (h.trans hO))
    (fun U h => restrictSections_smul θ U (h.trans hO))
    (fun U V hUV hV => restrictSections_res θ U V hUV (hV.trans hO))

/-- The sectionwise family of `restrictTo hO θ` is that of `θ`, on the opens contained in `O'`. -/
@[simp]
theorem restrictSections_restrictTo {O O' : X.Opens} (hO : O' ≤ O)
    (θ : Scheme.Modules.restrict M O.ι ⟶ Scheme.Modules.restrict N O.ι)
    (U : X.Opens) (h : U ≤ O') (m : Γ(M, U)) :
    restrictSections (restrictTo hO θ) U h m = restrictSections θ U (h.trans hO) m :=
  restrictSections_homOfRestrictSections _ _ _ _ _ U h m

/-- The action on sections of the restriction of a morphism `φ : M ⟶ N` to `O` is the action of
`φ` on the sections over the image. -/
theorem restrictHomApp_restrictFunctor_map (O : X.Opens) (φ : M ⟶ N)
    (U' : O.toScheme.Opens) (m : Γ(M, O.ι ''ᵁ U')) :
    restrictHomApp ((Scheme.Modules.restrictFunctor O.ι).map φ) U' m = φ.app (O.ι ''ᵁ U') m := by
  unfold restrictHomApp
  simp only [ConcreteCategory.comp_apply]
  rfl

/-- The sectionwise family of the restriction of a morphism `φ : M ⟶ N` to `O` is the action of
`φ` on sections. -/
@[simp]
theorem restrictSections_restrictFunctor_map (O : X.Opens) (φ : M ⟶ N) (U : X.Opens)
    (h : U ≤ O) (m : Γ(M, U)) :
    restrictSections ((Scheme.Modules.restrictFunctor O.ι).map φ) U h m = φ.app U m := by
  unfold restrictSections
  rw [restrictHomApp_restrictFunctor_map, ← Hom_app_presheaf_map φ (O.ι.image_preimage_le U) m,
    modules_presheaf_map_homOfLE_self]

/-- `restrictSections_restrictFunctor_map` in the `· .val.app (op U)` spelling. -/
theorem restrictSections_restrictFunctor_map_val (O : X.Opens) (φ : M ⟶ N) (U : X.Opens)
    (h : U ≤ O) (m : M.val.obj (op U)) :
    restrictSections ((Scheme.Modules.restrictFunctor O.ι).map φ) U h m = φ.val.app (op U) m :=
  restrictSections_restrictFunctor_map O φ U h m

end

end Stacks.AlgebraicGeometry.ModuleLimits

end
