module

public import StacksFrontier.AlgebraicGeometry.BaseAdicFiltration.Basic
public import StacksFrontier.RingTheory.Flat.ArtinLocalSquareZero

/-!
# Flatness of a family over an Artin local base

`Stacks.BaseAdicFiltration.flat_sections_of_flat` reads flatness of a morphism
`p : U ⟶ Spec A` off as flatness of its rings of sections. This file proves the converse and
feeds the ring-level criteria of `StacksFrontier/RingTheory/Flat/ArtinLocalSquareZero.lean` through
it, so that flatness of a family over an Artinian local base becomes a condition on each affine
open separately.

That is the direction an *existence* argument needs. The filtration argument of
[Stacks, Tag 0E3X] has flatness of the family as a hypothesis on the forward direction, where
`Stacks.BaseAdicFiltration.flat_sections_of_flat` and
`Stacks.BaseAdicFiltration.flat_stalk_of_flat` are the right tools; but its
essential-surjectivity direction *builds* a family over `Spec A`, by iterating [Stacks, Tag 05YV]
up the `𝔪`-adic tower of `Stacks.BaseAdicFiltration.exists_thickening_of_isArtinianRing`, and then
has to prove that family flat. The tower carries only a structure-sheaf identification as its
invariant, so the flatness is not propagated by it and has to be established at the top; nothing
in `Stacks.Thickenings.Realization` records it.

## Main results

* `Stacks.BaseAdicFiltration.flat_of_flat_sections`: a morphism to an affine scheme is flat as
  soon as the sections over every affine open form a flat module over the base ring. This is the
  converse of `Stacks.BaseAdicFiltration.flat_sections_of_flat`.
* `Stacks.BaseAdicFiltration.flat_iff_flat_sections`: the two together.
* `Stacks.BaseAdicFiltration.flat_of_injective_lsmul_sections`: over a local base whose maximal
  ideal squares to zero, a family is flat as soon as `𝔪 ⊗[A] Γ(V, W) → Γ(V, W)` is injective for
  every affine open `W`. This is the scheme-level form of
  `Module.Flat.iff_injective_lsmul_maximalIdeal`, and hence of [Stacks, Tag 063Y] in the shape an
  essential-surjectivity argument over a square-zero base consumes.
* `Stacks.BaseAdicFiltration.flat_of_isZero_Tor'_one_sections`: the same over a base whose
  maximal ideal is merely nilpotent, that is over an arbitrary Artinian local base, with the
  condition the vanishing of `Tor₁` against the residue field.

## Implementation notes

`AlgebraicGeometry.Flat` is affine-local at the source and at the target, and the target here is
`Spec A`, which is affine; so `AlgebraicGeometry.HasRingHomProperty.of_iSup_eq_top` reduces
flatness to the family of maps `Γ(Spec A, ⊤) ⟶ Γ(V, W)` indexed by the affine opens `W` of `V`.
Those are the maps `AlgebraicGeometry.Scheme.Hom.appLE`, and the `A`-algebra structure
`Stacks.BaseAdicFiltration.sectionsAlgebra` is that map precomposed with the inverse of
`AlgebraicGeometry.Scheme.ΓSpecIso`, an isomorphism — which is why the two notions of flatness
agree and why no stalk ever has to be looked at.

Going through stalks instead would work, by `AlgebraicGeometry.Flat.of_stalkMap`, but it would
force a comparison of two `A`-algebra structures on one stalk — the one induced by
`AlgebraicGeometry.Scheme.Hom.stalkMap` and `Stacks.BaseAdicFiltration.stalkAlgebra` — which is
exactly what the module docstring of `StacksFrontier/AlgebraicGeometry/BaseAdicFiltration/Basic.lean`
arranges for its consumers to avoid.

The low-priority instance `AlgebraicGeometry.Flat` carries for a subsingleton integral target does
not apply here. `Spec A` for `A` Artinian local is indeed one point, but it is integral only when
`A` is a field, and flatness over a non-reduced Artinian local ring is not automatic: over
`A = k[x]/x²` the residue field `k` is not a flat `A`-module.

## References

* [Stacks Project, Tag 063Y](https://stacks.math.columbia.edu/tag/063Y)
* [Stacks Project, Tag 0E3X](https://stacks.math.columbia.edu/tag/0E3X)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TensorProduct
open scoped AlgebraicGeometry

universe u

namespace Stacks.BaseAdicFiltration

variable {A : Type u} [CommRing A] {V : Scheme.{u}}

/-- The map on sections over an affine open, read as the structure map of
`Stacks.BaseAdicFiltration.sectionsAlgebra` precomposed with `AlgebraicGeometry.Scheme.ΓSpecIso`.

This is the equation `Stacks.BaseAdicFiltration.flat_sections_of_flat` uses in the other
direction; it holds by definition, the content being only that `sectionsAlgebra` is built from the
same `appLE`. -/
theorem appLE_hom_eq_algebraMap_comp (g : V ⟶ Spec (CommRingCat.of A)) (W : V.Opens) :
    letI := sectionsAlgebra g W
    (g.appLE ⊤ W le_top).hom =
      (algebraMap A Γ(V, W)).comp (Scheme.ΓSpecIso (.of A)).hom.hom := by
  let := sectionsAlgebra g W
  have hcancel : (Scheme.ΓSpecIso (.of A)).inv.hom.comp (Scheme.ΓSpecIso (.of A)).hom.hom
      = RingHom.id _ := by
    rw [← CommRingCat.hom_comp, Iso.hom_inv_id]
    rfl
  have hdef : (algebraMap A Γ(V, W))
      = (g.appLE ⊤ W le_top).hom.comp (Scheme.ΓSpecIso (.of A)).inv.hom := rfl
  rw [hdef, RingHom.comp_assoc, hcancel, RingHom.comp_id]

/-- **A family over an affine base is flat as soon as its rings of sections are flat.** For
`g : V ⟶ Spec A`, if the sections of `𝒪_V` over every affine open form a flat `A`-module, for the
`A`-algebra structure `Stacks.BaseAdicFiltration.sectionsAlgebra`, then `g` is flat.

This is the converse of `Stacks.BaseAdicFiltration.flat_sections_of_flat`. Flatness is
affine-local at the source and the target `Spec A` is affine, so the affine opens of `V` suffice;
see the implementation notes. -/
theorem flat_of_flat_sections (g : V ⟶ Spec (CommRingCat.of A))
    (h : ∀ W : V.affineOpens, letI := sectionsAlgebra g W.1; Module.Flat A Γ(V, W.1)) :
    AlgebraicGeometry.Flat g := by
  refine HasRingHomProperty.of_iSup_eq_top (P := @AlgebraicGeometry.Flat)
    (fun W : V.affineOpens => W) (iSup_affineOpens_eq_top V) fun W => ?_
  let := sectionsAlgebra g W.1
  have halg : RingHom.Flat (algebraMap A Γ(V, W.1)) := RingHom.flat_algebraMap_iff.mpr (h W)
  rw [appLE_hom_eq_algebraMap_comp g W.1]
  exact RingHom.Flat.comp
    (RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _)) halg

/-- **Flatness of a family over an affine base is flatness of its rings of sections.** The two
directions are `Stacks.BaseAdicFiltration.flat_sections_of_flat` and
`Stacks.BaseAdicFiltration.flat_of_flat_sections`. -/
theorem flat_iff_flat_sections (g : V ⟶ Spec (CommRingCat.of A)) :
    AlgebraicGeometry.Flat g ↔
      ∀ W : V.affineOpens, letI := sectionsAlgebra g W.1; Module.Flat A Γ(V, W.1) :=
  ⟨fun _ W => flat_sections_of_flat g W, flat_of_flat_sections g⟩

/-- **The flatness input over a square-zero base.** Let `A` be a local ring whose maximal ideal
squares to zero and let `g : V ⟶ Spec A` be any morphism. If for every affine open `W` of `V` the
multiplication map `𝔪 ⊗[A] Γ(V, W) → Γ(V, W)` is injective, then `g` is flat.

This is `Module.Flat.iff_injective_lsmul_maximalIdeal` sheafified along
`Stacks.BaseAdicFiltration.flat_of_flat_sections`: it is [Stacks, Tag 063Y] in the shape an
essential-surjectivity argument consumes, namely a bare `AlgebraicGeometry.Flat` for the
constructed family, with no hypothesis on the reduction of the family and no requirement that the
conormal comparison be surjective. -/
theorem flat_of_injective_lsmul_sections [IsLocalRing A]
    (hm : IsLocalRing.maximalIdeal A ^ 2 = ⊥) (g : V ⟶ Spec (CommRingCat.of A))
    (h : ∀ W : V.affineOpens, letI := sectionsAlgebra g W.1;
      Function.Injective (TensorProduct.lift
        ((LinearMap.lsmul A Γ(V, W.1)).comp (IsLocalRing.maximalIdeal A).subtype))) :
    AlgebraicGeometry.Flat g :=
  flat_of_flat_sections g fun W =>
    let := sectionsAlgebra g W.1
    (Module.Flat.iff_injective_lsmul_maximalIdeal hm Γ(V, W.1)).mpr (h W)

/-- **The flatness input over an arbitrary Artinian local base.** Let `A` be a local ring whose
maximal ideal is nilpotent — an Artinian local ring, for instance — and let
`g : V ⟶ Spec A` be any morphism. If `Tor₁^A(κ, Γ(V, W))` vanishes for every affine open `W` of
`V`, for `κ` the residue field of `A`, then `g` is flat.

This is `Module.Flat.iff_isZero_Tor'_one_residueField_of_isNilpotent` sheafified along
`Stacks.BaseAdicFiltration.flat_of_flat_sections`. It is the form that does not ask the maximal
ideal to square to zero, so it applies at the top of the `𝔪`-adic tower of
`Stacks.BaseAdicFiltration.exists_thickening_of_isArtinianRing` rather than only at one of its
steps. -/
theorem flat_of_isZero_Tor'_one_sections [IsLocalRing A]
    (hnil : IsNilpotent (IsLocalRing.maximalIdeal A)) (g : V ⟶ Spec (CommRingCat.of A))
    (h : ∀ W : V.affineOpens, letI := sectionsAlgebra g W.1;
      IsZero (((Tor' (ModuleCat.{u} A) 1).obj
        (ModuleCat.of A (A ⧸ IsLocalRing.maximalIdeal A))).obj (ModuleCat.of A Γ(V, W.1)))) :
    AlgebraicGeometry.Flat g :=
  flat_of_flat_sections g fun W =>
    let := sectionsAlgebra g W.1
    (Module.Flat.iff_isZero_Tor'_one_residueField_of_isNilpotent hnil Γ(V, W.1)).mpr (h W)

end Stacks.BaseAdicFiltration

end
