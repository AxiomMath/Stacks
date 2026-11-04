module

public import StacksFrontier.AlgebraicGeometry.ModuleLimits.HomGlue

/-!
# Glueing a morphism of sheaves of modules from morphisms of the restrictions

Let `M` and `N` be sheaves of modules on a scheme `X` and let `W` be a family of opens covering
`X`.  `Stacks.AlgebraicGeometry.ModuleLimits.exists_hom_app_eq_of_cover` glues a morphism
`M ⟶ N` out of *sectionwise* data over the members of `W`.  What a consumer holds is usually not
that, but a family of morphisms of the restrictions
`Scheme.Modules.restrict M (W a).ι ⟶ Scheme.Modules.restrict N (W a).ι`.  This file is the
dictionary between the two presentations, together with the glueing and the uniqueness statement
in the second one.

## Main definitions

* `Stacks.AlgebraicGeometry.ModuleLimits.restrictHomSection`: the action, on the sections over an
  open `U ≤ W`, of a morphism between the restrictions of `M` and `N` to `W`.  It is additive
  (`restrictHomSection_add`), `Γ(X, U)`-homogeneous (`restrictHomSection_smul`) and compatible
  with restriction along an inclusion of opens inside `W` (`restrictHomSection_res`), which is
  exactly what `exists_hom_app_eq_of_cover` asks of its local data.

## Main results

* `Stacks.AlgebraicGeometry.ModuleLimits.exists_restrictFunctor_map_eq_of_cover`: **glueing of a
  morphism of sheaves of modules out of morphisms of its restrictions.**  Given a family of opens
  covering `X` and, over each member `W a`, a morphism of the restrictions of `M` and `N` to
  `W a`, any two of which act in the same way on the sections over an open contained in both,
  there is a morphism `M ⟶ N` restricting to each of them.
* `Stacks.AlgebraicGeometry.ModuleLimits.eq_of_restrictFunctor_map_eq_of_cover`: the morphism so
  obtained is unique, since equality of morphisms of sheaves of modules is local.
* `Stacks.AlgebraicGeometry.ModuleLimits.restrictFunctor_map_eq_of_restrictHomSection`: two
  morphisms of the restrictions to `W` acting in the same way on the sections over every open
  contained in `W` are equal.
* `Stacks.AlgebraicGeometry.ModuleLimits.restrictHomSection_restrictFunctor_map`: the action on
  sections of the restriction of a morphism `M ⟶ N` is the action on sections of that morphism.

## Implementation notes

The sections of `Scheme.Modules.restrict M W.ι` over an open `V` of `W` are the sections of `M`
over `W.ι ''ᵁ V`, by `rfl`, and for `U ≤ W` the open `W.ι ''ᵁ (W.ι ⁻¹ᵁ U)` is `U`
(`Stacks.AlgebraicGeometry.ModuleLimits.image_preimage_of_le`) but only propositionally so.
Accordingly `restrictHomSection` is the composite of the restriction map along that equality of
opens, the action of the morphism on the sections over `W.ι ⁻¹ᵁ U`, and the restriction map back.

Although the identification of the two groups of sections holds by `rfl`, it is never left
implicit: every occurrence of it goes through the isomorphism
`AlgebraicGeometry.Scheme.Modules.restrictAppIso`, which is `Iso.refl` and comes with the
compatibilities with restriction and with scalar multiplication used throughout.  Leaving the
identification to definitional unfolding does typecheck, but it puts the resulting goals out of
reach of `rw` and `simp`, whose matching does not unfold `Scheme.Modules.restrict`.

The two transports are restriction maps `homOfLE` of the two inequalities underlying the equality
of opens, rather than `eqToHom`.  With that choice both `presheaf_map_homOfLE_comp` and
`Hom_app_presheaf_map` apply as they stand, and a composite of two restriction maps between the
same pair of opens collapses to the identity because a morphism of
`TopologicalSpace.Opens X` between fixed opens is unique.

## References

* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace Stacks.AlgebraicGeometry.ModuleLimits

/-- Restricting twice along inclusions of opens is restricting once, for the structure sheaf. -/
theorem scheme_presheaf_map_homOfLE_comp {X : Scheme.{u}} {U V Z : X.Opens} (h₁ : V ≤ U)
    (h₂ : Z ≤ V) (r : Γ(X, U)) :
    X.presheaf.map (homOfLE h₂).op (X.presheaf.map (homOfLE h₁).op r) =
      X.presheaf.map (homOfLE (h₂.trans h₁)).op r := by
  rw [← ConcreteCategory.comp_apply, ← X.presheaf.map_comp]
  congr 2

/-- Restricting a section of the structure sheaf along the inclusion of an open into itself does
nothing. -/
theorem scheme_presheaf_map_homOfLE_self {X : Scheme.{u}} {U : X.Opens} (h : U ≤ U)
    (r : Γ(X, U)) : X.presheaf.map (homOfLE h).op r = r := by
  simp

section

variable {X : Scheme.{u}} {M N : X.Modules}

/-- The image of an open of an open subscheme is contained in that open subscheme. -/
theorem image_ι_le {W : X.Opens} (V : W.toScheme.Opens) : W.ι ''ᵁ V ≤ W := by
  simpa using W.ι.image_le_opensRange V

/-- The action, on the sections over an open `U` contained in `W`, of a morphism between the
restrictions of `M` and `N` to `W`. -/
noncomputable def restrictHomSection {W : X.Opens}
    (χ : Scheme.Modules.restrict M W.ι ⟶ Scheme.Modules.restrict N W.ι)
    {U : X.Opens} (h : U ≤ W) (m : Γ(M, U)) : Γ(N, U) :=
  N.presheaf.map (homOfLE (image_preimage_of_le h).ge).op
    ((N.restrictAppIso W.ι (W.ι ⁻¹ᵁ U)).hom
      (χ.app (W.ι ⁻¹ᵁ U) ((M.restrictAppIso W.ι (W.ι ⁻¹ᵁ U)).inv
        (M.presheaf.map (homOfLE (image_preimage_of_le h).le).op m))))

/-- The restriction to `W` of a morphism `φ : M ⟶ N` acts on the sections over an open `V` of `W`
as `φ` acts on the sections over `W.ι ''ᵁ V`. -/
theorem restrictFunctor_map_app_apply (φ : M ⟶ N) {W : X.Opens} (V : W.toScheme.Opens)
    (x : Γ(M, W.ι ''ᵁ V)) :
    (N.restrictAppIso W.ι V).hom
        (((Scheme.Modules.restrictFunctor W.ι).map φ).app V
          ((M.restrictAppIso W.ι V).inv x)) = φ.app (W.ι ''ᵁ V) x :=
  rfl

/-- The action on sections of a morphism between the restrictions of `M` and `N` to `W` is
additive. -/
theorem restrictHomSection_add {W : X.Opens}
    (χ : Scheme.Modules.restrict M W.ι ⟶ Scheme.Modules.restrict N W.ι)
    {U : X.Opens} (h : U ≤ W) (m m' : Γ(M, U)) :
    restrictHomSection χ h (m + m') = restrictHomSection χ h m + restrictHomSection χ h m' := by
  simp only [restrictHomSection, map_add]

/-- The action on the sections over `U` of a morphism between the restrictions of `M` and `N` to
`W` is homogeneous for the sections of the structure sheaf over `U`. -/
theorem restrictHomSection_smul {W : X.Opens}
    (χ : Scheme.Modules.restrict M W.ι ⟶ Scheme.Modules.restrict N W.ι)
    {U : X.Opens} (h : U ≤ W) (r : Γ(X, U)) (m : Γ(M, U)) :
    restrictHomSection χ h (r • m) = r • restrictHomSection χ h m := by
  simp only [restrictHomSection, Scheme.Modules.map_smul,
    Scheme.Modules.smul_restrictAppIso_inv_apply, Scheme.Modules.Hom.app_smul,
    Scheme.Modules.smul_restrictAppIso_hom_apply, Iso.hom_inv_id_apply,
    scheme_presheaf_map_homOfLE_comp, scheme_presheaf_map_homOfLE_self]

/-- Restricting the image of a section of `M` over `U` to an open of `W` contained in `U` is
applying the morphism of the restrictions over that open.  This is the shape in which the
compatibility of `restrictHomSection` with restriction is used. -/
theorem presheaf_map_restrictHomSection {W : X.Opens}
    (χ : Scheme.Modules.restrict M W.ι ⟶ Scheme.Modules.restrict N W.ι)
    {U : X.Opens} (h : U ≤ W) (V : W.toScheme.Opens) (hV : W.ι ''ᵁ V ≤ U) (m : Γ(M, U)) :
    N.presheaf.map (homOfLE hV).op (restrictHomSection χ h m) =
      (N.restrictAppIso W.ι V).hom
        (χ.app V ((M.restrictAppIso W.ι V).inv (M.presheaf.map (homOfLE hV).op m))) := by
  have hk : V ≤ W.ι ⁻¹ᵁ U := (W.ι.preimage_image_eq V).ge.trans (W.ι.preimage_mono hV)
  rw [restrictHomSection, presheaf_map_homOfLE_comp,
    ← Scheme.Modules.map_restrictAppIso_hom_apply W.ι N (homOfLE hk).op,
    Hom_app_presheaf_map χ hk,
    Scheme.Modules.restrictAppIso_inv_map_apply W.ι M (homOfLE hk).op,
    presheaf_map_homOfLE_comp]

/-- Over the image of an open `V` of `W`, the action on sections of a morphism between the
restrictions of `M` and `N` to `W` is the action of that morphism over `V`. -/
theorem restrictHomSection_image {W : X.Opens}
    (χ : Scheme.Modules.restrict M W.ι ⟶ Scheme.Modules.restrict N W.ι)
    (V : W.toScheme.Opens) (h : W.ι ''ᵁ V ≤ W) (m : Γ(M, W.ι ''ᵁ V)) :
    restrictHomSection χ h m =
      (N.restrictAppIso W.ι V).hom (χ.app V ((M.restrictAppIso W.ι V).inv m)) := by
  simpa using presheaf_map_restrictHomSection χ h V le_rfl m

/-- The action on sections of a morphism between the restrictions of `M` and `N` to `W` commutes
with restriction along an inclusion of opens inside `W`. -/
theorem restrictHomSection_res {W : X.Opens}
    (χ : Scheme.Modules.restrict M W.ι ⟶ Scheme.Modules.restrict N W.ι)
    {U V : X.Opens} (hUV : U ≤ V) (hV : V ≤ W) (m : Γ(M, V)) :
    restrictHomSection χ (hUV.trans hV) (M.presheaf.map (homOfLE hUV).op m) =
      N.presheaf.map (homOfLE hUV).op (restrictHomSection χ hV m) := by
  have hsub : W.ι ''ᵁ (W.ι ⁻¹ᵁ U) ≤ V := (image_preimage_of_le (hUV.trans hV)).le.trans hUV
  rw [restrictHomSection, presheaf_map_homOfLE_comp,
    ← presheaf_map_restrictHomSection χ hV (W.ι ⁻¹ᵁ U) hsub m, presheaf_map_homOfLE_comp]

/-- The action on sections of the restriction of a morphism `φ : M ⟶ N` to `W` is the action on
sections of `φ`. -/
theorem restrictHomSection_restrictFunctor_map (φ : M ⟶ N) {W U : X.Opens} (h : U ≤ W)
    (m : Γ(M, U)) :
    restrictHomSection ((Scheme.Modules.restrictFunctor W.ι).map φ) h m = φ.app U m := by
  rw [restrictHomSection, restrictFunctor_map_app_apply, ← Hom_app_presheaf_map,
    presheaf_map_homOfLE_comp]
  simp

/-- Two morphisms between the restrictions of `M` and `N` to `W` are equal as soon as they act in
the same way on the sections over every open contained in `W`.  Every open of `W` is the preimage
of its image, so this is a statement about all of them. -/
theorem restrictFunctor_map_eq_of_restrictHomSection {W : X.Opens}
    {χ₁ χ₂ : Scheme.Modules.restrict M W.ι ⟶ Scheme.Modules.restrict N W.ι}
    (h : ∀ (U : X.Opens) (hU : U ≤ W) (m : Γ(M, U)),
      restrictHomSection χ₁ hU m = restrictHomSection χ₂ hU m) :
    χ₁ = χ₂ := by
  refine Scheme.Modules.hom_ext _ _ fun V => ?_
  ext x
  have key := (restrictHomSection_image χ₁ V (image_ι_le V)
      ((M.restrictAppIso W.ι V).hom x)).symm.trans
    ((h _ (image_ι_le V) _).trans (restrictHomSection_image χ₂ V (image_ι_le V) _))
  simp only [Iso.hom_inv_id_apply] at key
  simpa using congrArg (fun z => (N.restrictAppIso W.ι V).inv z) key

/-- **Glueing a morphism of sheaves of modules out of morphisms of its restrictions.**  Let `W`
be a family of opens covering the scheme `X` and suppose given, for each member, a morphism
`χ a : Scheme.Modules.restrict M (W a).ι ⟶ Scheme.Modules.restrict N (W a).ι`.  If `χ a` and
`χ b` act in the same way on the sections over every open contained in both `W a` and `W b`,
then there is a morphism `M ⟶ N` whose restriction to each member of the covering is the given
morphism.

The local data is converted to the sectionwise form by `restrictHomSection` and glued by
`Stacks.AlgebraicGeometry.ModuleLimits.exists_hom_app_eq_of_cover`; that the glued morphism
restricts to `χ a` is then a statement about its action on sections. -/
theorem exists_restrictFunctor_map_eq_of_cover {ι : Type u} (W : ι → X.Opens)
    (hW : ∀ x : X, ∃ a, x ∈ W a)
    (χ : ∀ a, Scheme.Modules.restrict M (W a).ι ⟶ Scheme.Modules.restrict N (W a).ι)
    (hagree : ∀ (a b : ι) (U : X.Opens) (ha : U ≤ W a) (hb : U ≤ W b) (m : Γ(M, U)),
      restrictHomSection (χ a) ha m = restrictHomSection (χ b) hb m) :
    ∃ φ : M ⟶ N, ∀ a, (Scheme.Modules.restrictFunctor (W a).ι).map φ = χ a := by
  obtain ⟨φ, hφ⟩ := exists_hom_app_eq_of_cover W hW (fun a _ h => restrictHomSection (χ a) h)
    (fun a _ h => restrictHomSection_add (χ a) h) (fun a _ h => restrictHomSection_smul (χ a) h)
    (fun a _ _ hUV hV => restrictHomSection_res (χ a) hUV hV) hagree
  refine ⟨φ, fun a => restrictFunctor_map_eq_of_restrictHomSection fun U hU m => ?_⟩
  rw [restrictHomSection_restrictFunctor_map, hφ a U hU m]

/-- The morphism produced by `exists_restrictFunctor_map_eq_of_cover` is unique: two morphisms
`M ⟶ N` with the same restrictions to the members of an open covering are equal. -/
theorem eq_of_restrictFunctor_map_eq_of_cover {ι : Type*} (W : ι → X.Opens)
    (hW : ∀ x : X, ∃ a, x ∈ W a) {φ ψ : M ⟶ N}
    {χ : ∀ a, Scheme.Modules.restrict M (W a).ι ⟶ Scheme.Modules.restrict N (W a).ι}
    (hφ : ∀ a, (Scheme.Modules.restrictFunctor (W a).ι).map φ = χ a)
    (hψ : ∀ a, (Scheme.Modules.restrictFunctor (W a).ι).map ψ = χ a) :
    φ = ψ :=
  hom_ext_of_restrict_cover W hW fun a => (hφ a).trans (hψ a).symm

end

end Stacks.AlgebraicGeometry.ModuleLimits

end
