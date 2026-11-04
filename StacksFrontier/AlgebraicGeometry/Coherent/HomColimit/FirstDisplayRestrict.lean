module

public import StacksFrontier.AlgebraicGeometry.Coherent.HomColimit.FirstDisplaySurjectivity

/-!
# The first display of Tag 01YB in terms of the geometric restriction functor

The first display of [Stacks, Tag 01YB] is proved in
`StacksFrontier.AlgebraicGeometry.Coherent.HomColimit.FirstDisplaySurjectivity` with the
restriction of a module to an open `U ⊆ X` taken in the sense of the Grothendieck slice,
`SheafOfModules.over U`, an object of `SheafOfModules (𝒪_X.over U)`. Its consumers restrict
instead along the open immersion `U.ι : U.toScheme ⟶ X`, giving an object of
`U.toScheme.Modules`. The two are different categories, so the statement in the slice form
cannot be applied to a morphism in the geometric form.

This file supplies the translation and restates the extension assertion of the first display in
the geometric form. The translation is Mathlib's `AlgebraicGeometry.Scheme.Modules.overEquiv`,
the equivalence between the two categories, together with
`AlgebraicGeometry.Scheme.Modules.overFunctorEquiv`, which identifies the slice restriction
functor composed with that equivalence with the geometric restriction functor.

## Main definitions

* `Stacks.AlgebraicGeometry.IdealPowerColimit.overEquivRestrictIso`: the comparison
  `(𝒪_X.over U)`-module `M.over U`, transported across `overEquiv U`, with the `𝒪_U`-module
  `M|_U`.
* `Stacks.AlgebraicGeometry.IdealPowerColimit.overPreimage`: the slice-form morphism
  `M.over U ⟶ N.over U` attached to a geometric-form morphism `M|_U ⟶ N|_U`.

## Main results

* `Stacks.AlgebraicGeometry.IdealPowerColimit.restrictFunctor_map_comp_eq_of_over`: an equation
  between slice-form morphisms transports to the corresponding equation between geometric-form
  morphisms.
* `Stacks.AlgebraicGeometry.IdealPowerColimit.isIso_restrictFunctor_map_idealPowerMultiple_ι`:
  the geometric restriction of the inclusion `Iⁿ M ⟶ M` to an open disjoint from the support of
  `I` is an isomorphism.
* `Stacks.AlgebraicGeometry.IdealPowerColimit.exists_hom_idealPowerMultiple_restrict_eq`: **the
  extension assertion of the first display of [Stacks, Tag 01YB], geometric form.** A morphism
  `G|_U ⟶ F|_U` over the complement `U` of `V(I)`, for `G` coherent and `F` quasi-coherent on a
  Noetherian scheme, is the restriction of a morphism `Iⁿ G ⟶ F` for some `n`.

## Implementation notes

The open is not required to be literally `I.support.compl`; it is taken as a variable together
with an equality to that open, so that a consumer whose open is presented differently — the
punctured spectrum of a local ring, say — can substitute its own description without first
rewriting the morphism it wants to extend.

The transport lemmas are stated for a variable open `U` rather than for `I.support.compl`
itself: the coercion `(I.support.compl : X.Opens)` elaborates at the type `Opens ↥X`, on which
the dot notation `.ι` of `AlgebraicGeometry.Scheme.Opens` is unavailable, so an open written out
that way cannot appear under the geometric restriction functor.

## References

* [Stacks Project, Tag 01YB](https://stacks.math.columbia.edu/tag/01YB)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open Stacks.AlgebraicGeometry.IdealPower

universe u

namespace Stacks.AlgebraicGeometry.IdealPowerColimit

variable {X : Scheme.{u}}

/-! ### Comparing the slice restriction with the geometric restriction -/

/-- **The slice restriction of `M` to `U`, transported to the open subscheme, is the geometric
restriction `M|_U`.**

This is the component at `M` of Mathlib's `AlgebraicGeometry.Scheme.Modules.overFunctorEquiv`,
the natural isomorphism identifying the slice restriction functor followed by the equivalence
`AlgebraicGeometry.Scheme.Modules.overEquiv U` with the restriction functor along the open
immersion `U.ι`. -/
public noncomputable def overEquivRestrictIso (U : X.Opens) (M : X.Modules) :
    (Scheme.Modules.overEquiv U).functor.obj (M.over U) ≅
      (Scheme.Modules.restrictFunctor U.ι).obj M :=
  (Scheme.Modules.overFunctorEquiv U).app M

/-- The comparison of the two restrictions is natural in the module: transporting the slice
restriction of a morphism and then comparing is comparing and then restricting
geometrically. -/
public theorem overEquivRestrictIso_naturality (U : X.Opens) {M N : X.Modules} (a : M ⟶ N) :
    (Scheme.Modules.overEquiv U).functor.map (a.over U) ≫ (overEquivRestrictIso U N).hom =
      (overEquivRestrictIso U M).hom ≫ (Scheme.Modules.restrictFunctor U.ι).map a :=
  (Scheme.Modules.overFunctorEquiv U).hom.naturality a

/-- **The slice-form morphism attached to a geometric-form morphism.** Conjugating `φ : M|_U ⟶
N|_U` by the comparison isomorphisms gives a morphism between the transports of the slice
restrictions, and the functor of `AlgebraicGeometry.Scheme.Modules.overEquiv U` is full, so that
morphism is the transport of a — necessarily unique — morphism `M.over U ⟶ N.over U`. -/
public noncomputable def overPreimage (U : X.Opens) {M N : X.Modules}
    (φ : (Scheme.Modules.restrictFunctor U.ι).obj M ⟶
      (Scheme.Modules.restrictFunctor U.ι).obj N) : M.over U ⟶ N.over U :=
  (Scheme.Modules.overEquiv U).functor.preimage
    ((overEquivRestrictIso U M).hom ≫ φ ≫ (overEquivRestrictIso U N).inv)

/-- The transport of `overPreimage U φ`, followed by the comparison isomorphism, is the
comparison isomorphism followed by `φ`: the slice-form morphism really does recover `φ`. -/
public theorem map_overPreimage_comp (U : X.Opens) {M N : X.Modules}
    (φ : (Scheme.Modules.restrictFunctor U.ι).obj M ⟶
      (Scheme.Modules.restrictFunctor U.ι).obj N) :
    (Scheme.Modules.overEquiv U).functor.map (overPreimage U φ) ≫
        (overEquivRestrictIso U N).hom =
      (overEquivRestrictIso U M).hom ≫ φ := by
  rw [overPreimage, (Scheme.Modules.overEquiv U).functor.map_preimage]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- **Transport of a factorisation across the comparison.** If the slice restriction of
`a : M ⟶ N` followed by the slice-form morphism attached to `φ : N|_U ⟶ P|_U` is the slice
restriction of `b : M ⟶ P`, then the geometric restriction of `a` followed by `φ` is the
geometric restriction of `b`.

Both sides are compared with their slice counterparts by `overEquivRestrictIso_naturality`, and
the comparison at `M` is an isomorphism, hence cancellable. -/
public theorem restrictFunctor_map_comp_eq_of_over (U : X.Opens) {M N P : X.Modules}
    (a : M ⟶ N) (b : M ⟶ P)
    (φ : (Scheme.Modules.restrictFunctor U.ι).obj N ⟶
      (Scheme.Modules.restrictFunctor U.ι).obj P)
    (key : a.over U ≫ overPreimage U φ = b.over U) :
    (Scheme.Modules.restrictFunctor U.ι).map a ≫ φ =
      (Scheme.Modules.restrictFunctor U.ι).map b := by
  refine (Iso.cancel_iso_hom_left (overEquivRestrictIso U M) _ _).mp ?_
  calc (overEquivRestrictIso U M).hom ≫ (Scheme.Modules.restrictFunctor U.ι).map a ≫ φ
      = (Scheme.Modules.overEquiv U).functor.map (a.over U) ≫
          (overEquivRestrictIso U N).hom ≫ φ := by
        rw [← Category.assoc, ← overEquivRestrictIso_naturality U a, Category.assoc]
    _ = (Scheme.Modules.overEquiv U).functor.map (a.over U) ≫
          (Scheme.Modules.overEquiv U).functor.map (overPreimage U φ) ≫
          (overEquivRestrictIso U P).hom := by
        rw [map_overPreimage_comp U φ]
    _ = (Scheme.Modules.overEquiv U).functor.map (b.over U) ≫
          (overEquivRestrictIso U P).hom := by
        rw [← Category.assoc, ← Functor.map_comp, key]
    _ = (overEquivRestrictIso U M).hom ≫ (Scheme.Modules.restrictFunctor U.ι).map b :=
        overEquivRestrictIso_naturality U b

/-- A morphism whose slice restriction to `U` is an isomorphism has an invertible geometric
restriction to `U`: the two restrictions are compared by an isomorphism natural in the
module. -/
public theorem isIso_restrictFunctor_map_of_isIso_over (U : X.Opens) {M N : X.Modules}
    (a : M ⟶ N) (h : IsIso (a.over U)) :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map a) := by
  have hmap : IsIso ((Scheme.Modules.overEquiv U).functor.map (a.over U) ≫
      (overEquivRestrictIso U N).hom) :=
    have := h
    inferInstance
  rw [overEquivRestrictIso_naturality] at hmap
  have := hmap
  exact IsIso.of_isIso_comp_left (overEquivRestrictIso U M).hom _

/-- **`(Iⁿ M)|_U ≅ M|_U` in the geometric form**, for `U` an open disjoint from the support of
`I`: away from the closed subscheme cut out by `I` the unit ideal already generates, so the
inclusion `Iⁿ M ⟶ M` restricts to an isomorphism there. This is
`Stacks.AlgebraicGeometry.IdealPowerColimit.isIso_idealPowerMultiple_ι_over` read through the
comparison of the two restrictions. -/
public theorem isIso_restrictFunctor_map_idealPowerMultiple_ι (I : X.IdealSheafData) (n : ℕ)
    (M : X.Modules) {U : X.Opens} (hU : Disjoint (U : Set X) (I.support : Set X)) :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map (idealPowerMultiple I n M).ι) :=
  isIso_restrictFunctor_map_of_isIso_over U _ (isIso_idealPowerMultiple_ι_over I n M hU)

/-! ### The first display, geometric form -/

/-- **The extension assertion of the first display of [Stacks, Tag 01YB], in terms of the
geometric restriction functor.** Let `X` be a Noetherian scheme, `I` a quasi-coherent sheaf of
ideals, `U` the complement of the closed subscheme it cuts out, `G` a coherent `𝒪_X`-module and
`F` a quasi-coherent `𝒪_X`-module. Every morphism `G|_U ⟶ F|_U` of `𝒪_U`-modules is, for some
`n`, the restriction of a morphism `Iⁿ G ⟶ F` of `𝒪_X`-modules, in the sense that
precomposition with the restricted inclusion `(Iⁿ G)|_U ⟶ G|_U` turns it into that morphism's
restriction.

Surjectivity of the first display,
`Stacks.AlgebraicGeometry.IdealPowerColimit.exists_homRestrict_eq`, is the same assertion with
the restriction taken in the Grothendieck slice; the content here is only the transport across
`AlgebraicGeometry.Scheme.Modules.overEquiv`. -/
public theorem exists_hom_idealPowerMultiple_restrict_eq [AlgebraicGeometry.IsNoetherian X]
    (I : X.IdealSheafData) (U : X.Opens) (hU : U = I.support.compl)
    (G F : X.Modules) [G.IsCoherent] [F.IsQuasicoherent]
    (φ : (Scheme.Modules.restrictFunctor U.ι).obj G ⟶
      (Scheme.Modules.restrictFunctor U.ι).obj F) :
    ∃ (n : ℕ) (ψ : idealPowSmul I n G ⟶ F),
      (Scheme.Modules.restrictFunctor U.ι).map (idealPowerMultiple I n G).ι ≫ φ =
        (Scheme.Modules.restrictFunctor U.ι).map ψ := by
  subst hU
  obtain ⟨n, ψ, hψ⟩ := exists_homRestrict_eq I G F (overPreimage _ φ)
  exact ⟨n, ψ, restrictFunctor_map_comp_eq_of_over _ _ _ φ
    (hψ ▸ Iso.hom_inv_id_assoc
      (idealPowSmulOverIso I n G (disjoint_supportCompl_support I)) _)⟩

end Stacks.AlgebraicGeometry.IdealPowerColimit

end
