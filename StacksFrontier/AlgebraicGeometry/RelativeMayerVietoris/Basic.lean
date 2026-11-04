module

public import StacksFrontier.AlgebraicGeometry.RelativeMayerVietoris.Restriction

/-!
# Degree-zero relative Mayer–Vietoris

Let `X` be a scheme, let `U` and `V` be opens of `X` and let `F` be an `𝒪_X`-module. Writing
`j_W : W ⟶ X` for the inclusion of an open and `Φ_W := j_{W,*} j_W^* F`
(`Stacks.AlgebraicGeometry.RelativeMayerVietoris.pushRestrict`), this file proves that

`Φ_{U ⊔ V} ≅ ker (Φ_U ⊞ Φ_V ⟶ Φ_{U ⊓ V})`,

the map being the difference of the two restrictions. On sections over an open `T` this is exactly
the sheaf condition for `F` and the two-element cover `{U ⊓ T, V ⊓ T}` of `(U ⊔ V) ⊓ T`.

This is the degree-`0` case of relative Mayer–Vietoris, the exact sequence displayed in the proof
of [Stacks, Tag 01LC](https://stacks.math.columbia.edu/tag/01LC); pushing it forward along a
morphism `f : X ⟶ S` is free, because `f_*` is a right adjoint and therefore preserves kernels.

## Main results

* `Stacks.AlgebraicGeometry.RelativeMayerVietoris.mvDiff`: the difference of the two restrictions
  `Φ_U ⊞ Φ_V ⟶ Φ_{U ⊓ V}`.
* `Stacks.AlgebraicGeometry.RelativeMayerVietoris.mvRes`: the pair of restrictions
  `Φ_{U ⊔ V} ⟶ Φ_U ⊞ Φ_V`.
* `Stacks.AlgebraicGeometry.RelativeMayerVietoris.mvRes_comp_mvDiff`: the composite is zero.
* `Stacks.AlgebraicGeometry.RelativeMayerVietoris.mayerVietorisIso`: **the isomorphism**
  `Φ_{U ⊔ V} ≅ ker (mvDiff)`.
* `Stacks.AlgebraicGeometry.RelativeMayerVietoris.mayerVietorisIso_hom_comp_ι`: the isomorphism,
  followed by the kernel inclusion, is the pair of restrictions `mvRes`, so it is the map the
  exact sequence of the source names.

## Implementation notes

The isomorphism is obtained by checking that the canonical map into the kernel is an isomorphism,
and isomorphisms of `𝒪_X`-modules are detected on sections
(`AlgebraicGeometry.Scheme.Modules.Hom.isIso_iff_isIso_app`); on sections one then has to produce a
bijection of abelian groups. Injectivity is the separatedness half of the sheaf condition and
surjectivity is the gluing half, both supplied by
`StacksFrontier.AlgebraicGeometry.RelativeMayerVietoris.Restriction` once `resPush_app` has
identified the restriction morphisms on sections.

Sections of a biproduct are handled by `biprod_app_total`, which is `biprod.total` evaluated at a
section: it writes a section of `Φ_U ⊞ Φ_V` as the sum of the images of its two components, so no
identification of `Γ(Φ_U ⊞ Φ_V, T)` with a product of abelian groups is needed.

The sections of `Φ_W` over `T` are the sections of `F` over `W.ι ''ᵁ (W.ι ⁻¹ᵁ T)`, and the two
spellings agree only after unfolding semireducible definitions. Consequently the proofs that cross
between them are written in term mode, where the elaborator works at default transparency; the
corresponding `rw` steps fail. The `mvFst`, `mvSnd`, `mvInl`, `mvInr` abbreviations exist only so
that the type ascriptions on `biprod.fst` and friends do not have to be repeated: as `abbrev`s
they are reducible, so the `biprod` simp lemmas still apply to them.

## References

* [Stacks Project, Tag 01LC](https://stacks.math.columbia.edu/tag/01LC)
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace Stacks.AlgebraicGeometry.RelativeMayerVietoris

variable {X : Scheme.{u}}

/-! ### The two remaining inequalities of opens -/

/-- The open `(U ⊔ V) ⊓ T` is covered by `U ⊓ T` and `V ⊓ T`, in the spelling in which these are
the opens over which the Mayer–Vietoris modules have their sections. -/
theorem sup_image_preimage_le (U V T : X.Opens) :
    (U ⊔ V).ι ''ᵁ ((U ⊔ V).ι ⁻¹ᵁ T) ≤ U.ι ''ᵁ (U.ι ⁻¹ᵁ T) ⊔ V.ι ''ᵁ (V.ι ⁻¹ᵁ T) := by
  rw [ι_image_preimage, ι_image_preimage, ι_image_preimage, inf_sup_right]

/-- The intersection of `U ⊓ T` and `V ⊓ T` is contained in `(U ⊓ V) ⊓ T`, in the same
spelling. -/
theorem inf_image_preimage_le (U V T : X.Opens) :
    U.ι ''ᵁ (U.ι ⁻¹ᵁ T) ⊓ V.ι ''ᵁ (V.ι ⁻¹ᵁ T) ≤ (U ⊓ V).ι ''ᵁ ((U ⊓ V).ι ⁻¹ᵁ T) := by
  rw [ι_image_preimage, ι_image_preimage, ι_image_preimage]
  exact fun x hx => ⟨⟨hx.1.1, hx.2.1⟩, hx.1.2⟩

/-! ### Elementary facts about sections of morphisms -/

/-- Applying a composite to a section is applying the factors in turn. -/
theorem app_comp_apply {M N K : X.Modules} (φ : M ⟶ N) (ψ : N ⟶ K) (T : X.Opens) (x : Γ(M, T)) :
    ψ.app T (φ.app T x) = (φ ≫ ψ).app T x :=
  rfl

/-- The negative of a morphism of `𝒪_X`-modules on sections. -/
theorem neg_app {M N : X.Modules} (φ : M ⟶ N) (T : X.Opens) : (-φ).app T = -φ.app T := by
  rw [← zero_sub, Scheme.Modules.Hom.sub_app, Scheme.Modules.Hom.zero_app, zero_sub]

/-- **`biprod.total` on sections.** A section of `M ⊞ N` over `T` is the sum of the images of its
two components. -/
theorem biprod_app_total {M N : X.Modules} (T : X.Opens) (z : Γ(M ⊞ N, T)) :
    (biprod.inl : M ⟶ M ⊞ N).app T ((biprod.fst : M ⊞ N ⟶ M).app T z)
      + (biprod.inr : N ⟶ M ⊞ N).app T ((biprod.snd : M ⊞ N ⟶ N).app T z) = z := by
  have e : ((biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr : M ⊞ N ⟶ M ⊞ N)).app T z
      = Scheme.Modules.Hom.app (𝟙 (M ⊞ N)) T z :=
    congr($(biprod.total (X := M) (Y := N)).app T z)
  rw [Scheme.Modules.Hom.add_app, AddCommGrpCat.hom_add_apply, Scheme.Modules.Hom.id_app,
    ConcreteCategory.id_apply] at e
  rw [app_comp_apply, app_comp_apply]
  exact e

/-- The two projections of a biproduct are jointly injective on sections. -/
theorem biprod_app_ext {M N : X.Modules} (T : X.Opens) {z w : Γ(M ⊞ N, T)}
    (h₁ : (biprod.fst : M ⊞ N ⟶ M).app T z = (biprod.fst : M ⊞ N ⟶ M).app T w)
    (h₂ : (biprod.snd : M ⊞ N ⟶ N).app T z = (biprod.snd : M ⊞ N ⟶ N).app T w) : z = w := by
  rw [← biprod_app_total T z, ← biprod_app_total T w, h₁, h₂]

/-! ### The Mayer–Vietoris maps -/

variable (F : X.Modules) (U V : X.Opens)

/-- The first projection of `Φ_U ⊞ Φ_V`, with its type fixed. -/
noncomputable abbrev mvFst : pushRestrict F U ⊞ pushRestrict F V ⟶ pushRestrict F U := biprod.fst

/-- The second projection of `Φ_U ⊞ Φ_V`, with its type fixed. -/
noncomputable abbrev mvSnd : pushRestrict F U ⊞ pushRestrict F V ⟶ pushRestrict F V := biprod.snd

/-- The first inclusion into `Φ_U ⊞ Φ_V`, with its type fixed. -/
noncomputable abbrev mvInl : pushRestrict F U ⟶ pushRestrict F U ⊞ pushRestrict F V := biprod.inl

/-- The second inclusion into `Φ_U ⊞ Φ_V`, with its type fixed. -/
noncomputable abbrev mvInr : pushRestrict F V ⟶ pushRestrict F U ⊞ pushRestrict F V := biprod.inr

/-- **The difference of the two restrictions** `Φ_U ⊞ Φ_V ⟶ Φ_{U ⊓ V}`. Its kernel is the
degree-`0` relative Mayer–Vietoris object. -/
noncomputable def mvDiff : pushRestrict F U ⊞ pushRestrict F V ⟶ pushRestrict F (U ⊓ V) :=
  biprod.desc (resPush F inf_le_left) (-resPush F inf_le_right)

/-- **The pair of restrictions** `Φ_{U ⊔ V} ⟶ Φ_U ⊞ Φ_V`. -/
noncomputable def mvRes : pushRestrict F (U ⊔ V) ⟶ pushRestrict F U ⊞ pushRestrict F V :=
  biprod.lift (resPush F le_sup_left) (resPush F le_sup_right)

/-- The two restrictions of a section of `Φ_{U ⊔ V}` agree on `U ⊓ V`: the Mayer–Vietoris square
commutes. -/
theorem mvRes_comp_mvDiff : mvRes F U V ≫ mvDiff F U V = 0 := by
  rw [mvRes, mvDiff, biprod.lift_desc, Preadditive.comp_neg, resPush_comp, resPush_comp,
    add_neg_cancel]

/-- The first component of `mvRes` is the restriction `Φ_{U ⊔ V} ⟶ Φ_U`. -/
@[simp] theorem mvRes_comp_fst : mvRes F U V ≫ mvFst F U V = resPush F le_sup_left :=
  biprod.lift_fst _ _

/-- The second component of `mvRes` is the restriction `Φ_{U ⊔ V} ⟶ Φ_V`. -/
@[simp] theorem mvRes_comp_snd : mvRes F U V ≫ mvSnd F U V = resPush F le_sup_right :=
  biprod.lift_snd _ _

/-- `mvDiff` restricted to `Φ_U` is the restriction `Φ_U ⟶ Φ_{U ⊓ V}`. -/
@[simp] theorem inl_comp_mvDiff : mvInl F U V ≫ mvDiff F U V = resPush F inf_le_left :=
  biprod.inl_desc _ _

/-- `mvDiff` restricted to `Φ_V` is minus the restriction `Φ_V ⟶ Φ_{U ⊓ V}`. -/
@[simp] theorem inr_comp_mvDiff : mvInr F U V ≫ mvDiff F U V = -resPush F inf_le_right :=
  biprod.inr_desc _ _

/-! ### The sheaf condition on sections -/

/-- The first component of `mvRes` on sections is the restriction to `U ⊓ T`. -/
theorem mvRes_app_fst (T : X.Opens) (x : Γ(pushRestrict F (U ⊔ V), T)) :
    (mvFst F U V).app T ((mvRes F U V).app T x) =
      res F (image_preimage_mono le_sup_left T) x := by
  have h : (mvRes F U V ≫ mvFst F U V).app T = res F (image_preimage_mono le_sup_left T) := by
    rw [mvRes_comp_fst, resPush_app]
  exact (app_comp_apply _ _ T x).trans (congr($h x))

/-- The second component of `mvRes` on sections is the restriction to `V ⊓ T`. -/
theorem mvRes_app_snd (T : X.Opens) (x : Γ(pushRestrict F (U ⊔ V), T)) :
    (mvSnd F U V).app T ((mvRes F U V).app T x) =
      res F (image_preimage_mono le_sup_right T) x := by
  have h : (mvRes F U V ≫ mvSnd F U V).app T = res F (image_preimage_mono le_sup_right T) := by
    rw [mvRes_comp_snd, resPush_app]
  exact (app_comp_apply _ _ T x).trans (congr($h x))

/-- **Separatedness.** `mvRes` is injective on sections: a section of `Φ_{U ⊔ V}` is determined by
its restrictions to `U` and `V`. -/
theorem injective_mvRes_app (T : X.Opens) : Function.Injective ((mvRes F U V).app T) :=
  fun x y hxy => eq_of_res_eq₂ F (sup_image_preimage_le U V T)
    (image_preimage_mono le_sup_left T) (image_preimage_mono le_sup_right T) x y
    (((mvRes_app_fst F U V T x).symm.trans
      (congrArg (fun z => (mvFst F U V).app T z) hxy)).trans (mvRes_app_fst F U V T y))
    (((mvRes_app_snd F U V T x).symm.trans
      (congrArg (fun z => (mvSnd F U V).app T z) hxy)).trans (mvRes_app_snd F U V T y))

/-- `mvDiff` on the image of the first inclusion is the restriction to `U ⊓ V`. -/
theorem mvDiff_app_inl (T : X.Opens) (x : Γ(pushRestrict F U, T)) :
    (mvDiff F U V).app T ((mvInl F U V).app T x) =
      res F (image_preimage_mono inf_le_left T) x := by
  have h : (mvInl F U V ≫ mvDiff F U V).app T = res F (image_preimage_mono inf_le_left T) := by
    rw [inl_comp_mvDiff, resPush_app]
  exact (app_comp_apply _ _ T x).trans (congr($h x))

/-- `mvDiff` on the image of the second inclusion is minus the restriction to `U ⊓ V`. -/
theorem mvDiff_app_inr (T : X.Opens) (x : Γ(pushRestrict F V, T)) :
    (mvDiff F U V).app T ((mvInr F U V).app T x) =
      -res F (image_preimage_mono inf_le_right T) x := by
  have h : (mvInr F U V ≫ mvDiff F U V).app T =
      -res F (image_preimage_mono inf_le_right T) := by
    rw [inr_comp_mvDiff, neg_app, resPush_app]
    rfl
  exact (app_comp_apply _ _ T x).trans (congr($h x))

/-- **Gluing.** A section of `Φ_U ⊞ Φ_V` killed by the difference of the restrictions comes from a
section of `Φ_{U ⊔ V}`. -/
theorem exists_mvRes_app (T : X.Opens) (b : Γ(pushRestrict F U ⊞ pushRestrict F V, T))
    (hb : (mvDiff F U V).app T b = 0) : ∃ a, (mvRes F U V).app T a = b := by
  have hsum : (mvDiff F U V).app T ((mvInl F U V).app T ((mvFst F U V).app T b))
      + (mvDiff F U V).app T ((mvInr F U V).app T ((mvSnd F U V).app T b)) = 0 := by
    rw [← map_add, biprod_app_total T b, hb]
  rw [mvDiff_app_inl, mvDiff_app_inr] at hsum
  obtain ⟨a, ha₁, ha₂⟩ := exists_gluing₂ F (sup_image_preimage_le U V T)
    (image_preimage_mono le_sup_left T) (image_preimage_mono le_sup_right T)
    (image_preimage_mono inf_le_left T) (image_preimage_mono inf_le_right T)
    (inf_image_preimage_le U V T) ((mvFst F U V).app T b) ((mvSnd F U V).app T b)
    (add_neg_eq_zero.mp hsum)
  exact ⟨a, biprod_app_ext T ((mvRes_app_fst F U V T a).trans ha₁)
    ((mvRes_app_snd F U V T a).trans ha₂)⟩

/-! ### The isomorphism -/

/-- The canonical map from `Φ_{U ⊔ V}` to the kernel of the difference of the restrictions. -/
noncomputable def mvKernelLift : pushRestrict F (U ⊔ V) ⟶ kernel (mvDiff F U V) :=
  kernel.lift _ (mvRes F U V) (mvRes_comp_mvDiff F U V)

/-- The canonical map into the kernel, followed by the kernel inclusion, is `mvRes`. -/
@[reassoc (attr := simp)]
theorem mvKernelLift_comp_ι : mvKernelLift F U V ≫ kernel.ι _ = mvRes F U V :=
  kernel.lift_ι _ _ _

/-- **The degree-`0` relative Mayer–Vietoris isomorphism**, in the form that the canonical map
into the kernel is invertible. -/
instance isIso_mvKernelLift : IsIso (mvKernelLift F U V) := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro T
  rw [ConcreteCategory.isIso_iff_bijective]
  have hfac : ∀ x, (kernel.ι (mvDiff F U V)).app T ((mvKernelLift F U V).app T x)
      = (mvRes F U V).app T x := fun x =>
    (app_comp_apply _ _ T x).trans (congr($(mvKernelLift_comp_ι F U V).app T x))
  have hinj : Function.Injective ((kernel.ι (mvDiff F U V)).app T) :=
    injective_app_of_mono _ T
  refine ⟨fun x y hxy => injective_mvRes_app F U V T ?_, fun y => ?_⟩
  · rw [← hfac x, ← hfac y, hxy]
  · have h0 : (mvDiff F U V).app T ((kernel.ι (mvDiff F U V)).app T y) = 0 := by
      rw [app_comp_apply, kernel.condition, Scheme.Modules.Hom.zero_app]
      exact AddCommGrpCat.zero_apply _ _ y
    obtain ⟨a, ha⟩ := exists_mvRes_app F U V T _ h0
    exact ⟨a, hinj ((hfac a).trans ha)⟩

/-- **Degree-`0` relative Mayer–Vietoris.** For opens `U` and `V` of a scheme `X` and an
`𝒪_X`-module `F`, the direct image of the restriction of `F` to `U ⊔ V` is the kernel of the
difference of the two restrictions

`j_{U,*} j_U^* F ⊞ j_{V,*} j_V^* F ⟶ j_{U ⊓ V,*} j_{U ⊓ V}^* F`.

On sections over an open `T` this is the sheaf condition for the two-element cover
`{U ⊓ T, V ⊓ T}` of `(U ⊔ V) ⊓ T`. -/
noncomputable def mayerVietorisIso :
    pushRestrict F (U ⊔ V) ≅ kernel (mvDiff F U V) :=
  asIso (mvKernelLift F U V)

/-- The forward map of `mayerVietorisIso` is `mvKernelLift`. -/
@[simp] theorem mayerVietorisIso_hom : (mayerVietorisIso F U V).hom = mvKernelLift F U V := rfl

/-- The Mayer–Vietoris isomorphism is the pair of restrictions. -/
@[reassoc (attr := simp)]
theorem mayerVietorisIso_hom_comp_ι :
    (mayerVietorisIso F U V).hom ≫ kernel.ι _ = mvRes F U V :=
  mvKernelLift_comp_ι F U V

end Stacks.AlgebraicGeometry.RelativeMayerVietoris

end
