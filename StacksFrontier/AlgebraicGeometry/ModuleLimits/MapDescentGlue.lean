module

public import StacksFrontier.AlgebraicGeometry.ModuleLimits.HomGlue
/-!
# Zariski glueing of a morphism of sheaves of modules out of morphisms of restrictions

Given an open covering `W` of a scheme `X` and morphisms of restrictions
`Scheme.Modules.restrict M (W a).ι ⟶ Scheme.Modules.restrict N (W a).ι` that agree on the
pairwise intersections, there is a morphism `M ⟶ N` restricting to each of them. Glueing
morphisms, as opposed to glueing modules, needs only this agreement, with no cocycle condition.
This is the glueing step of [Stacks Project, Tag 01ZR] (2) in the general quasi-compact
quasi-separated case.

## Main definitions

* `Stacks.AlgebraicGeometry.ModuleLimits.imageSections`: the action on sections of a morphism
  of restrictions `M|_W ⟶ N|_W`, read over an open `U` of the ambient scheme presented as the
  image `W.ι ''ᵁ P` of an open `P` of `W`.
* `Stacks.AlgebraicGeometry.ModuleLimits.restrictHomOfLE`: the restriction of a morphism of
  restrictions `M|_W ⟶ N|_W` to a smaller open `V ≤ W`, as a morphism `M|_V ⟶ N|_V`.

## Main results

* `Stacks.AlgebraicGeometry.ModuleLimits.exists_restrictFunctor_map_eq_of_cover_of_imageSections`:
  given an open covering `W` of `X` and morphisms `χ a : M|_{W a} ⟶ N|_{W a}` whose actions on
  sections, read through `Stacks.AlgebraicGeometry.ModuleLimits.imageSections`, agree over every
  open contained in two members of the covering, there is a morphism `φ : M ⟶ N` restricting to
  `χ a` on each member.
* `Stacks.AlgebraicGeometry.ModuleLimits.exists_restrictFunctor_map_eq_of_cover_of_inf`: the
  same, with the agreement hypothesis an equality of the two restrictions of `χ a` and `χ b` to
  `W a ⊓ W b`.
* `Stacks.AlgebraicGeometry.ModuleLimits.imageSections_restrictHomOfLE`: the action on
  sections is unchanged by passing to a smaller open.

## References

* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace Stacks.AlgebraicGeometry.ModuleLimits

variable {X : Scheme.{u}} {M N : X.Modules}

/-! ### The action on sections of a morphism of restrictions -/

/-- Mathlib's comparison between the sections of a restriction and the sections of the module
over the image open is the identity. -/
theorem restrictAppIso_eq_refl {Y Z : Scheme.{u}} (f : Y ⟶ Z) [IsOpenImmersion f]
    (K : Z.Modules) (U : Y.Opens) : Scheme.Modules.restrictAppIso f K U = Iso.refl _ := rfl

/-- The action on sections of a morphism `χ : M|_W ⟶ N|_W` between the restrictions of `M` and
`N` to an open `W`, over an open `U` of `X` presented as the image `W.ι ''ᵁ P` of an open `P`
of `W`. -/
noncomputable def imageSections {W : X.Opens}
    (χ : Scheme.Modules.restrict M W.ι ⟶ Scheme.Modules.restrict N W.ι)
    {U : X.Opens} {P : W.toScheme.Opens} (hP : W.ι ''ᵁ P = U) :
    Γ(M, U) → Γ(N, U) :=
  match U, hP with
  | _, rfl => fun m => (Scheme.Modules.restrictAppIso W.ι N P).hom
      (χ.app P ((Scheme.Modules.restrictAppIso W.ι M P).inv m))

/-- `imageSections` on the image of an open `P` of `W` is the action of `χ` on sections over `P`,
conjugated by `AlgebraicGeometry.Scheme.Modules.restrictAppIso`. -/
@[simp]
theorem imageSections_rfl {W : X.Opens}
    (χ : Scheme.Modules.restrict M W.ι ⟶ Scheme.Modules.restrict N W.ι)
    (P : W.toScheme.Opens) (m : Γ(M, W.ι ''ᵁ P)) :
    imageSections χ (rfl : W.ι ''ᵁ P = W.ι ''ᵁ P) m =
      (Scheme.Modules.restrictAppIso W.ι N P).hom
        (χ.app P ((Scheme.Modules.restrictAppIso W.ι M P).inv m)) :=
  rfl

/-- `imageSections` on the image of an open of `W` is the action of `χ` on sections. -/
theorem imageSections_rfl_app {W : X.Opens}
    (χ : Scheme.Modules.restrict M W.ι ⟶ Scheme.Modules.restrict N W.ι)
    (P : W.toScheme.Opens) (m : Γ(M, W.ι ''ᵁ P)) :
    imageSections χ (rfl : W.ι ''ᵁ P = W.ι ''ᵁ P) m = χ.app P m := by
  simp only [imageSections_rfl, restrictAppIso_eq_refl, Iso.refl_hom, Iso.refl_inv]
  rfl

/-- `imageSections` is additive. -/
theorem imageSections_add {W : X.Opens}
    (χ : Scheme.Modules.restrict M W.ι ⟶ Scheme.Modules.restrict N W.ι)
    {U : X.Opens} {P : W.toScheme.Opens} (hP : W.ι ''ᵁ P = U) (m m' : Γ(M, U)) :
    imageSections χ hP (m + m') = imageSections χ hP m + imageSections χ hP m' := by
  subst hP
  simp

/-- `imageSections` is `Γ(X, U)`-homogeneous. -/
theorem imageSections_smul {W : X.Opens}
    (χ : Scheme.Modules.restrict M W.ι ⟶ Scheme.Modules.restrict N W.ι)
    {U : X.Opens} {P : W.toScheme.Opens} (hP : W.ι ''ᵁ P = U) (r : Γ(X, U))
    (m : Γ(M, U)) :
    imageSections χ hP (r • m) = r • imageSections χ hP m := by
  subst hP
  simp only [imageSections_rfl, Scheme.Modules.smul_restrictAppIso_inv_apply,
    Scheme.Modules.Hom.app_smul, Scheme.Modules.smul_restrictAppIso_hom_apply,
    Scheme.Opens.ι_appIso, Iso.refl_hom, Iso.refl_inv]
  rfl

/-- `imageSections` commutes with restriction along an inclusion of opens. -/
theorem imageSections_presheaf_map {W : X.Opens}
    (χ : Scheme.Modules.restrict M W.ι ⟶ Scheme.Modules.restrict N W.ι)
    {U V : X.Opens} {P Q : W.toScheme.Opens} (hP : W.ι ''ᵁ P = U) (hQ : W.ι ''ᵁ Q = V)
    (hUV : U ≤ V) (m : Γ(M, V)) :
    imageSections χ hP (M.presheaf.map (homOfLE hUV).op m)
      = N.presheaf.map (homOfLE hUV).op (imageSections χ hQ m) := by
  subst hP hQ
  exact (Hom_app_presheaf_map χ ((W.ι.image_le_image_iff P Q).mp hUV) m).symm

/-- `imageSections` does not depend on the presentation of `U` as an image. -/
theorem imageSections_congr {W : X.Opens}
    (χ : Scheme.Modules.restrict M W.ι ⟶ Scheme.Modules.restrict N W.ι)
    {U : X.Opens} {P Q : W.toScheme.Opens} (hP : W.ι ''ᵁ P = U) (hQ : W.ι ''ᵁ Q = U)
    (m : Γ(M, U)) : imageSections χ hP m = imageSections χ hQ m := by
  obtain rfl := W.ι.image_injective (hP.trans hQ.symm)
  rfl

/-! ### Restricting a morphism of restrictions to a smaller open -/

/-- The restriction of a morphism `χ : M|_W ⟶ N|_W` to a smaller open `V ≤ W`, as a morphism
`M|_V ⟶ N|_V`, assembled from the action of `χ` on sections by `homOfSections`. -/
noncomputable def restrictHomOfLE {V W : X.Opens} (e : V ≤ W)
    (χ : Scheme.Modules.restrict M W.ι ⟶ Scheme.Modules.restrict N W.ι) :
    Scheme.Modules.restrict M V.ι ⟶ Scheme.Modules.restrict N V.ι :=
  homOfSections (M := Scheme.Modules.restrict M V.ι) (N := Scheme.Modules.restrict N V.ι)
    (fun P x => (Scheme.Modules.restrictAppIso V.ι N P).inv
      (imageSections χ (image_preimage_of_le ((V.ι_image_le P).trans e))
        ((Scheme.Modules.restrictAppIso V.ι M P).hom x)))
    (fun _ _ _ => by
      simp only [map_add, imageSections_add])
    (fun _ _ _ => by
      simp only [Scheme.Modules.smul_restrictAppIso_hom_apply, imageSections_smul,
        Scheme.Modules.smul_restrictAppIso_inv_apply, Scheme.Opens.ι_appIso, Iso.refl_hom,
        Iso.refl_inv]
      rfl)
    (fun P Q h _ => by
      rw [Scheme.Modules.map_restrictAppIso_hom_apply,
        imageSections_presheaf_map χ (image_preimage_of_le ((V.ι_image_le P).trans e))
          (image_preimage_of_le ((V.ι_image_le Q).trans e)) (Scheme.Hom.image_mono V.ι h),
        Scheme.Modules.restrictAppIso_inv_map_apply])

/-- The action of `restrictHomOfLE e χ` on the sections over the image of an open of `V` is the
action of `χ`. -/
theorem imageSections_restrictHomOfLE_rfl {V W : X.Opens} (e : V ≤ W)
    (χ : Scheme.Modules.restrict M W.ι ⟶ Scheme.Modules.restrict N W.ι)
    (P : V.toScheme.Opens) (m : Γ(M, V.ι ''ᵁ P)) :
    imageSections (restrictHomOfLE e χ) (rfl : V.ι ''ᵁ P = V.ι ''ᵁ P) m
      = imageSections χ (image_preimage_of_le ((V.ι_image_le P).trans e)) m := by
  simp only [imageSections_rfl, restrictHomOfLE, homOfSections_app, restrictAppIso_eq_refl,
    Iso.refl_hom, Iso.refl_inv]
  rfl

/-- **Restricting a morphism of restrictions to a smaller open does not change its action on
sections.** -/
theorem imageSections_restrictHomOfLE {V W : X.Opens} (e : V ≤ W)
    (χ : Scheme.Modules.restrict M W.ι ⟶ Scheme.Modules.restrict N W.ι)
    {U : X.Opens} {P : V.toScheme.Opens} {Q : W.toScheme.Opens}
    (hP : V.ι ''ᵁ P = U) (hQ : W.ι ''ᵁ Q = U) (m : Γ(M, U)) :
    imageSections (restrictHomOfLE e χ) hP m = imageSections χ hQ m := by
  subst hP
  rw [imageSections_restrictHomOfLE_rfl]
  exact imageSections_congr χ _ _ m

/-! ### The glueing, at the level of morphisms -/

/-- **Zariski glueing of a morphism of sheaves of modules out of morphisms of restrictions.**
Let `W` be a family of opens covering `X` and let `χ a : M|_{W a} ⟶ N|_{W a}` be morphisms of
the restrictions whose actions on sections agree over every open contained in two members of the
family. Then there is a morphism `φ : M ⟶ N` whose restriction to `W a` is `χ a`. -/
theorem exists_restrictFunctor_map_eq_of_cover_of_imageSections {ι : Type u} (W : ι → X.Opens)
    (hW : ∀ x : X, ∃ a, x ∈ W a)
    (χ : ∀ a, Scheme.Modules.restrict M (W a).ι ⟶ Scheme.Modules.restrict N (W a).ι)
    (hagree : ∀ (a b : ι) (U : X.Opens) (ha : U ≤ W a) (hb : U ≤ W b) (m : Γ(M, U)),
      imageSections (χ a) (image_preimage_of_le ha) m
        = imageSections (χ b) (image_preimage_of_le hb) m) :
    ∃ φ : M ⟶ N, ∀ a, (Scheme.Modules.restrictFunctor (W a).ι).map φ = χ a := by
  obtain ⟨φ, hφ⟩ := exists_hom_app_eq_of_cover W hW
    (fun a U h => imageSections (χ a) (image_preimage_of_le h))
    (fun a U h => imageSections_add (χ a) (image_preimage_of_le h))
    (fun a U h => imageSections_smul (χ a) (image_preimage_of_le h))
    (fun a U V hUV hV => imageSections_presheaf_map (χ a) (image_preimage_of_le
      (hUV.trans hV)) (image_preimage_of_le hV) hUV)
    (fun a b U ha hb => hagree a b U ha hb)
  refine ⟨φ, fun a => Scheme.Modules.hom_ext _ _ fun P => ?_⟩
  ext (m : Γ(M, (W a).ι ''ᵁ P))
  show φ.app ((W a).ι ''ᵁ P) m = (χ a).app P m
  rw [hφ a ((W a).ι ''ᵁ P) ((W a).ι_image_le P) m,
    imageSections_congr (χ a) _ (rfl : (W a).ι ''ᵁ P = (W a).ι ''ᵁ P) m,
    imageSections_rfl_app]

/-- **Zariski glueing of a morphism of sheaves of modules out of morphisms of restrictions
agreeing on the pairwise intersections of the covering.** Let `W` be a family of opens covering
`X` and let `χ a : M|_{W a} ⟶ N|_{W a}` be morphisms of the restrictions such that the
restrictions of `χ a` and `χ b` to `W a ⊓ W b` are equal. Then there is a morphism `φ : M ⟶ N`
whose restriction to `W a` is `χ a`. -/
theorem exists_restrictFunctor_map_eq_of_cover_of_inf {ι : Type u} (W : ι → X.Opens)
    (hW : ∀ x : X, ∃ a, x ∈ W a)
    (χ : ∀ a, Scheme.Modules.restrict M (W a).ι ⟶ Scheme.Modules.restrict N (W a).ι)
    (hagree : ∀ a b, restrictHomOfLE (inf_le_left : W a ⊓ W b ≤ W a) (χ a)
      = restrictHomOfLE (inf_le_right : W a ⊓ W b ≤ W b) (χ b)) :
    ∃ φ : M ⟶ N, ∀ a, (Scheme.Modules.restrictFunctor (W a).ι).map φ = χ a := by
  refine exists_restrictFunctor_map_eq_of_cover_of_imageSections W hW χ
    fun a b U ha hb m => ?_
  rw [← imageSections_restrictHomOfLE (inf_le_left : W a ⊓ W b ≤ W a) (χ a)
      (image_preimage_of_le (le_inf ha hb)) (image_preimage_of_le ha) m,
    hagree a b,
    imageSections_restrictHomOfLE (inf_le_right : W a ⊓ W b ≤ W b) (χ b)
      (image_preimage_of_le (le_inf ha hb)) (image_preimage_of_le hb) m]

end Stacks.AlgebraicGeometry.ModuleLimits

end
