module

public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.Denominators
public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.ChartSaturation

/-!
# A meromorphic section regular at a point is regular on a neighbourhood

The penultimate paragraph of [Stacks, Tag 0BD7] computes, at a point `x` of `X`, the *germ* of
the meromorphic section `φ^*(q) s` and finds it to be a unit times the germ of a generator of
`ℒ` there — in particular that germ lies in the image of `ℒ_x` inside `𝒦_X(ℒ)_x`. What
`Stacks.InvertiblePullback.IsPullMeromorphicFamilyOn` asks for instead is a genuine section
`t` of `ℒ` on an open `V ∋ x` with `φ^*(q) s = t` there. This file is that passage, and nothing
else: the nearest existing statement,
`AlgebraicGeometry.mono_toMeromorphicSectionSheafAsModule`, gives injectivity of
`ℒ ⟶ 𝒦_X(ℒ)`, which says a section is determined by its image, not that an image exists.

The argument is the universal property of a stalk and nothing more. Two sections of `𝒦_X(ℒ)`
with the same germ at `x` agree on some neighbourhood of `x` (`TopCat.Presheaf.germ_eq`), and
the image of a section of `ℒ` restricts to the image of its restriction, by naturality of
`AlgebraicGeometry.toMeromorphicSectionSheafAsModule`. No integrality and no invertibility is
used.

## Main results

* `AlgebraicGeometry.exists_restrictₛₗ_eq_toMeromorphicSectionSheafAsModule_of_grpGerm_eq`: a
  meromorphic section whose germ at `x` is the germ of the image of a section `t'` of `ℒ` is,
  on a neighbourhood of `x`, the image of a restriction of `t'`.
* `AlgebraicGeometry.exists_restrictₛₗ_eq_toMeromorphicSectionSheafAsModule_of_grpGerm_mem_range`:
  the same with the hypothesis as membership of the germ in the range of the stalk map
  `ℒ_x → 𝒦_X(ℒ)_x`, which is the form in which the penultimate paragraph produces it.
* `AlgebraicGeometry.exists_mem_generatingLocus_restrictₛₗ_eq_toMeromorphicSectionSheafAsModule`:
  with the germ a *unit* multiple of the germ of a generating section, the section produced
  still generates at the point — the two conjuncts a member of
  `Stacks.InvertiblePullback.IsPullMeromorphicFamilyOn` owes at one point of `X`.

## Implementation notes

`TopCat.Presheaf.germ_eq` returns its two inclusions as morphisms of the category of opens
rather than as `≤`. They are turned back into `homOfLE` of `CategoryTheory.leOfHom`, which is
the identity on a preorder category, so the restriction maps need no transport.

What is still owed to use the last result is its hypothesis `hgerm`: the germ at `x` of
`φ^*(q) s` as a unit multiple of the germ of a chart generator. On an *integral* `X` that germ
identity can be traded for one in the single stalk at the generic point, by
`AlgebraicGeometry.eq_toMeromorphicSectionSheafAsModule_iff_eq_germ`; what is missing there is
the generic value of a `𝒦_X`-multiple `a • σ`: the scalar law
`AlgebraicGeometry.constantGenericStalkModuleSection_smul` together with a reading of
`a ∈ 𝒦_X(U)` as an element of `K(X)`.

No tag attribute: [Stacks, Tag 0BD7] makes no statement about one point of `X`.

## References

* [Stacks Project, Tag 0BD7](https://stacks.math.columbia.edu/tag/0BD7)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}
    (L : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))

/-- **A meromorphic section whose germ is the germ of a regular section is regular nearby.** If
the germ at `x` of `σ ∈ 𝒦_X(ℒ)(W)` is the germ of the image of `t' ∈ ℒ(W')`, then on some open
`V ∋ x` contained in both, `σ` is the image of the restriction of `t'`. -/
theorem exists_restrictₛₗ_eq_toMeromorphicSectionSheafAsModule_of_grpGerm_eq
    {W W' : Opens X.toRingedSpace.carrier} {x : X.toRingedSpace.carrier}
    (hxW : x ∈ W) (hxW' : x ∈ W')
    (σ : (meromorphicSectionSheafAsModule X L).val.obj (op W)) (t' : L.val.obj (op W'))
    (hgerm : grpGerm X.toRingedSpace (meromorphicSectionSheafAsModule X L).val x W hxW σ
      = grpGerm X.toRingedSpace (meromorphicSectionSheafAsModule X L).val x W' hxW'
          ((toMeromorphicSectionSheafAsModule X L).val.app (op W') t')) :
    ∃ (V : Opens X.toRingedSpace.carrier) (hVW : V ≤ W) (hVW' : V ≤ W'), x ∈ V ∧
      (meromorphicSectionSheafAsModule X L).val.restrictₛₗ (homOfLE hVW).op σ
        = (toMeromorphicSectionSheafAsModule X L).val.app (op V)
            (L.val.restrictₛₗ (homOfLE hVW').op t') := by
  obtain ⟨V, hxV, iW, iW', heq⟩ :=
    TopCat.Presheaf.germ_eq (C := AddCommGrpCat.{u})
      (meromorphicSectionSheafAsModule X L).val.presheaf x hxW hxW' σ _ hgerm
  refine ⟨V, leOfHom iW, leOfHom iW', hxV, heq.trans ?_⟩
  exact (PresheafOfModules.naturality_apply (toMeromorphicSectionSheafAsModule X L).val
    (homOfLE (leOfHom iW')).op t').symm

/-- The stalk map of the inclusion `ℒ ⟶ 𝒦_X(ℒ)` sends the germ of `t'` to the germ of its image. -/
private theorem stalkMap_grpGerm_eq_grpGerm_app
    {W : Opens X.toRingedSpace.carrier} {x : X.toRingedSpace.carrier} (hxW : x ∈ W)
    (t : L.val.obj (op W)) :
    stalkMap X.toRingedSpace L.val (meromorphicSectionSheafAsModule X L).val
        (toMeromorphicSectionSheafAsModule X L).val x (grpGerm X.toRingedSpace L.val x W hxW t)
      = grpGerm X.toRingedSpace (meromorphicSectionSheafAsModule X L).val x W hxW
          ((toMeromorphicSectionSheafAsModule X L).val.app (op W) t) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply (C := AddCommGrpCat.{u}) W x hxW
    ((PresheafOfModules.toPresheaf _).map (toMeromorphicSectionSheafAsModule X L).val) t

/-- **The same with the hypothesis read in the stalk.** A meromorphic section whose germ at `x`
lies in the image of `ℒ_x` is the image of a section of `ℒ` on a neighbourhood of `x`. This is
the form the penultimate paragraph of [Stacks, Tag 0BD7] produces: it computes the germ, not a
section. -/
theorem exists_restrictₛₗ_eq_toMeromorphicSectionSheafAsModule_of_grpGerm_mem_range
    {W : Opens X.toRingedSpace.carrier} {x : X.toRingedSpace.carrier} (hxW : x ∈ W)
    (σ : (meromorphicSectionSheafAsModule X L).val.obj (op W))
    (hmem : grpGerm X.toRingedSpace (meromorphicSectionSheafAsModule X L).val x W hxW σ ∈
      AddMonoidHom.range (stalkMap X.toRingedSpace L.val
        (meromorphicSectionSheafAsModule X L).val
        (toMeromorphicSectionSheafAsModule X L).val x)) :
    ∃ (V : Opens X.toRingedSpace.carrier) (hVW : V ≤ W), x ∈ V ∧
      ∃ t : L.val.obj (op V),
        (meromorphicSectionSheafAsModule X L).val.restrictₛₗ (homOfLE hVW).op σ
          = (toMeromorphicSectionSheafAsModule X L).val.app (op V) t := by
  obtain ⟨l, hl⟩ := hmem
  obtain ⟨W', hxW', t', ht'⟩ :=
    TopCat.Presheaf.exists_germ_eq (C := AddCommGrpCat.{u}) L.val.presheaf l
  obtain ⟨V, hVW, hVW', hxV, hV⟩ :=
    exists_restrictₛₗ_eq_toMeromorphicSectionSheafAsModule_of_grpGerm_eq L hxW hxW' σ t'
      (hl.symm.trans ((congrArg _ ht'.symm).trans (stalkMap_grpGerm_eq_grpGerm_app L hxW' t')))
  exact ⟨V, hVW, hxV, L.val.restrictₛₗ (homOfLE hVW').op t', hV⟩

/-- **The conclusion the penultimate paragraph of [Stacks, Tag 0BD7] owes, from its germ
identity.** If the germ at `x` of a meromorphic section `σ` of `ℒ` is a *unit* multiple of the
germ of a section `t'` generating `ℒ` at `x`, then on an open `V ∋ x` the section `σ` is the
image of a section of `ℒ` which still generates at `x`. The two conjuncts asked of a member of
`Stacks.InvertiblePullback.IsPullMeromorphicFamilyOn` at the point `x` are exactly these. -/
theorem exists_mem_generatingLocus_restrictₛₗ_eq_toMeromorphicSectionSheafAsModule
    {W U : Opens X.toRingedSpace.carrier} {x : X.toRingedSpace.carrier}
    (hxW : x ∈ W) (hxU : x ∈ U)
    (σ : (meromorphicSectionSheafAsModule X L).val.obj (op W)) (t' : L.val.obj (op U))
    (ht' : x ∈ Stacks.SheafOfModules.generatingLocus L t')
    {u : ringStalk X.toRingedSpace x} (hu : IsUnit u)
    (hgerm : grpGerm X.toRingedSpace (meromorphicSectionSheafAsModule X L).val x W hxW σ
      = stalkMap X.toRingedSpace L.val (meromorphicSectionSheafAsModule X L).val
          (toMeromorphicSectionSheafAsModule X L).val x
          (u • grpGerm X.toRingedSpace L.val x U hxU t')) :
    ∃ (V : Opens X.toRingedSpace.carrier) (hVW : V ≤ W), x ∈ V ∧
      ∃ t : L.val.obj (op V), x ∈ Stacks.SheafOfModules.generatingLocus L t ∧
        (meromorphicSectionSheafAsModule X L).val.restrictₛₗ (homOfLE hVW).op σ
          = (toMeromorphicSectionSheafAsModule X L).val.app (op V) t := by
  obtain ⟨W₀, hxW₀, c, hc⟩ := X.presheaf.exists_germ_eq u
  have hxU₁ : x ∈ U ⊓ W₀ := ⟨hxU, hxW₀⟩
  -- The unit germ, spread to a section on `U ⊓ W₀`, times the restriction of `t'`.
  have hgermc : ringGerm X.toRingedSpace x (U ⊓ W₀) hxU₁
      (X.presheaf.map (homOfLE (inf_le_right : U ⊓ W₀ ≤ W₀)).op c) = u :=
    (TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE inf_le_right) x hxU₁ c).trans hc
  have hgermt : grpGerm X.toRingedSpace L.val x (U ⊓ W₀) hxU₁
        (L.val.restrictₛₗ (homOfLE (inf_le_left : U ⊓ W₀ ≤ U)).op t')
      = grpGerm X.toRingedSpace L.val x U hxU t' :=
    TopCat.Presheaf.germ_res_apply (C := AddCommGrpCat.{u}) L.val.presheaf
      (homOfLE inf_le_left) x hxU₁ t'
  have hprod : grpGerm X.toRingedSpace L.val x (U ⊓ W₀) hxU₁
        (X.presheaf.map (homOfLE (inf_le_right : U ⊓ W₀ ≤ W₀)).op c •
          L.val.restrictₛₗ (homOfLE (inf_le_left : U ⊓ W₀ ≤ U)).op t')
      = u • grpGerm X.toRingedSpace L.val x U hxU t' :=
    (stalkModule_germ_smul X.toRingedSpace L.val x (U ⊓ W₀) hxU₁ _ _).trans
      (congrArg₂ (· • ·) hgermc hgermt)
  obtain ⟨V, hVW, hVU₁, hxV, hV⟩ :=
    exists_restrictₛₗ_eq_toMeromorphicSectionSheafAsModule_of_grpGerm_eq L hxW hxU₁ σ _
      (hgerm.trans ((congrArg _ hprod.symm).trans (stalkMap_grpGerm_eq_grpGerm_app L hxU₁ _)))
  refine ⟨V, hVW, hxV, _, ?_, hV⟩
  refine Stacks.SheafOfModules.mem_generatingLocus_of_grpGerm_eq_smul L hxV hxU hu ?_ ht'
  exact (TopCat.Presheaf.germ_res_apply (C := AddCommGrpCat.{u}) L.val.presheaf
    (homOfLE hVU₁) x hxV _).trans hprod

end AlgebraicGeometry

end
