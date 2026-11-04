module

public import Mathlib.AlgebraicGeometry.Limits
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme
public import StacksFrontier.AlgebraicGeometry.SquareRootCover.DenominatorAlgebra

@[expose] public noncomputable section

/-!
# (SQ) for an arbitrary scheme

This file proves, for an arbitrary scheme `X`, an arbitrary open subset `Ω` and an arbitrary
section `u` of the structure sheaf over `Ω`:

> **(SQ)** there is a surjective integral morphism `f : A ⟶ X` such that at every point `p` of
> `A` lying over `Ω` the image of `u` in `𝒪_{A, p}` is a square.

Since an integral morphism is affine, `A` is the relative spectrum of a quasi-coherent integral
`𝒪_X`-algebra, so this is the statement that the general case of [Stacks, Tag 0CNZ] turns on;
see the module documentation of
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.FppfApplication.IntegralDomination`. It is **not**
a tagged statement of its own, and the implication to Tag 0CNZ is not formal.

## Main results

* `Stacks.SquareRootCover.exists_isIntegralHom_surjective_isSquare_germ_of_mem`: **(SQ)**, with
  the conclusion at every point of `A` lying over `Ω`.
* `Stacks.SquareRootCover.exists_isIntegralHom_surjective_isSquare_germ_general`: the same
  statement at the points over a fixed point `x` of `Ω`, matching the shape of the affine case
  `Stacks.SquareRootCover.exists_isIntegralHom_surjective_isSquare_germ`.
* `Stacks.SquareRootCover.exists_isIntegralHom_surjective_isSquare_stalkMap_general`: the
  literal `f.stalkMap` reading of the latter.

## Implementation notes

The construction is the one recorded in
`StacksFrontier.RingTheory.ModuleQuadraticExtension`. There is one reduction and then the
algebra: let `Y` be the reduced closed subscheme on the closure of `Ω` and `Z` the reduced
closed subscheme on the closed complement of `Ω`. Both `Y ⟶ X` and `Z ⟶ X` are closed
immersions, hence integral, their images cover `X`, and no point of `Z` lies over `Ω`. In `Y`
the open subset `Ω` is dense, so
`Stacks.SquareRootCover.exists_isIntegralHom_surjective_isSquare_germ_of_dense` applies to
`Y`, and `A ⨿ Z ⟶ X` is the required morphism.

Only one reduction is needed, not two: the reduced closed subscheme on the closure of `Ω` is
reduced *and* has `Ω` dense in it, so the passage to `X_red` is subsumed.

## References

* [Stacks Project, Tag 0CNZ](https://stacks.math.columbia.edu/tag/0CNZ)
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.SquareRootCover

/-- If a closed immersion has as image the closure of an open subset `Ω`, then the preimage of
`Ω` is dense in its source: the image of its closure is closed and contains `Ω`, hence is the
whole image. -/
lemma dense_preimage_of_range_eq_closure {Y X : Scheme.{u}} (ι : Y ⟶ X) [IsClosedImmersion ι]
    {Ω : X.Opens} (hr : Set.range ι = closure (Ω : Set X)) :
    Dense ((ι ⁻¹ᵁ Ω : Y.Opens) : Set Y) := by
  have hemb := IsClosedImmersion.isClosedEmbedding ι
  have h1 : (ι : Y → X) '' (ι ⁻¹' (Ω : Set X)) = (Ω : Set X) := by
    rw [Set.image_preimage_eq_inter_range, hr, Set.inter_eq_left]
    exact subset_closure
  have h2 : closure ((ι : Y → X) '' (ι ⁻¹' (Ω : Set X)))
      = (ι : Y → X) '' closure (ι ⁻¹' (Ω : Set X)) := hemb.closure_image_eq _
  rw [h1] at h2
  rw [show ((ι ⁻¹ᵁ Ω : Y.Opens) : Set Y) = ι ⁻¹' (Ω : Set X) from rfl, dense_iff_closure_eq]
  refine hemb.injective.image_injective ?_
  rw [← h2, Set.image_univ, hr]

/-- The reduced closed subscheme on a closed subset `T`: it is reduced and its image is `T`. -/
private lemma exists_isReduced_isClosedImmersion_range_eq (X : Scheme.{u}) (T : Closeds X) :
    ∃ (Y : Scheme.{u}) (_ : IsReduced Y) (ι : Y ⟶ X) (_ : IsClosedImmersion ι),
      Set.range ι = (T : Set X) :=
  ⟨(Scheme.IdealSheafData.vanishingIdeal T).subscheme, inferInstance,
    (Scheme.IdealSheafData.vanishingIdeal T).subschemeι, inferInstance,
    Scheme.IdealSheafData.range_subschemeι_vanishingIdeal _⟩

/-- The reduced closed subscheme on the closure of an open subset `Ω`: it is reduced, its image
is the closure of `Ω`, and `Ω` is dense in it. -/
lemma exists_isClosedImmersion_range_eq_closure (X : Scheme.{u}) (Ω : X.Opens) :
    ∃ (Y : Scheme.{u}) (_ : IsReduced Y) (ι : Y ⟶ X) (_ : IsClosedImmersion ι),
      Set.range ι = closure (Ω : Set X) ∧ Dense ((ι ⁻¹ᵁ Ω : Y.Opens) : Set Y) := by
  obtain ⟨Y, hY, ι, hι, hr⟩ := exists_isReduced_isClosedImmersion_range_eq X
    ⟨closure (Ω : Set X), isClosed_closure⟩
  exact ⟨Y, hY, ι, hι, hr, dense_preimage_of_range_eq_closure ι hr⟩

/-- The reduced closed subscheme on the closed complement of an open subset `Ω`. -/
lemma exists_isClosedImmersion_range_eq_compl (X : Scheme.{u}) (Ω : X.Opens) :
    ∃ (Z : Scheme.{u}) (ι : Z ⟶ X) (_ : IsClosedImmersion ι),
      Set.range ι = (Ω : Set X)ᶜ := by
  obtain ⟨Z, -, ι, hι, hr⟩ := exists_isReduced_isClosedImmersion_range_eq X
    ⟨(Ω : Set X)ᶜ, Ω.isOpen.isClosed_compl⟩
  exact ⟨Z, ι, hι, hr⟩

/-- Transport of the conclusion of (SQ) along an equality of morphisms. -/
lemma isSquare_germ_app_congr {A X : Scheme.{u}} {f f' : A ⟶ X} (hff : f = f')
    {Ω : X.Opens} (s : Γ(X, Ω)) (p : A) (hp : f.base p ∈ Ω) (hp' : f'.base p ∈ Ω)
    (h : IsSquare (A.presheaf.germ (f' ⁻¹ᵁ Ω) p hp' (f'.app Ω s))) :
    IsSquare (A.presheaf.germ (f ⁻¹ᵁ Ω) p hp (f.app Ω s)) := by
  subst hff
  exact h

/-- **(SQ) for an arbitrary scheme.** For every scheme `X`, every open subset `Ω` and every
section `u` of the structure sheaf over `Ω` there is a surjective integral morphism
`f : A ⟶ X` such that at every point `p` of `A` lying over `Ω` the image of `u` in the local
ring of `A` at `p` is a square.

The morphism is `Spec_Y(𝒪_Y ⊕ ℐ) ⨿ Z ⟶ X`, where `Y` is the reduced closed subscheme on the
closure of `Ω`, `ℐ` is the ideal of denominators of `u` on `Y` and `Z` is the reduced closed
subscheme on the complement of `Ω`. -/
theorem exists_isIntegralHom_surjective_isSquare_germ_of_mem (X : Scheme.{u}) (Ω : X.Opens)
    (u : Γ(X, Ω)) :
    ∃ (A : Scheme.{u}) (f : A ⟶ X), IsIntegralHom f ∧ Surjective f ∧
      ∀ (p : A) (hp : f.base p ∈ Ω),
        IsSquare (A.presheaf.germ (f ⁻¹ᵁ Ω) p hp (f.app Ω u)) := by
  obtain ⟨Y, hYred, ιY, hιY, hYrange, hYdense⟩ :=
    exists_isClosedImmersion_range_eq_closure X Ω
  obtain ⟨Z, ιZ, hιZ, hZrange⟩ := exists_isClosedImmersion_range_eq_compl X Ω
  have := hYred
  have := hιY
  have := hιZ
  obtain ⟨A₀, g, hgint, hgsurj, hgsq⟩ :=
    exists_isIntegralHom_surjective_isSquare_germ_of_dense (X := Y) (Ω := ιY ⁻¹ᵁ Ω)
      (u := ιY.app Ω u) (hΩ := hYdense)
  have := hgint
  have := hgsurj
  refine ⟨A₀ ⨿ Z, coprod.desc (g ≫ ιY) ιZ, inferInstance, ⟨fun y => ?_⟩, fun p hp => ?_⟩
  · by_cases hy : y ∈ (Ω : Set X)
    · obtain ⟨b, hb⟩ : y ∈ Set.range ιY := by
        rw [hYrange]; exact subset_closure hy
      obtain ⟨a, ha⟩ := hgsurj.surj b
      refine ⟨(coprod.inl : A₀ ⟶ A₀ ⨿ Z) a, ?_⟩
      rw [← Scheme.Hom.comp_apply, coprod.inl_desc, Scheme.Hom.comp_apply, ha, hb]
    · obtain ⟨c, hc⟩ : y ∈ Set.range ιZ := by rw [hZrange]; exact hy
      refine ⟨(coprod.inr : Z ⟶ A₀ ⨿ Z) c, ?_⟩
      rw [← Scheme.Hom.comp_apply, coprod.inr_desc, hc]
  · have hcov : Set.range (coprod.inl : A₀ ⟶ A₀ ⨿ Z) ∪
        Set.range (coprod.inr : Z ⟶ A₀ ⨿ Z) = Set.univ :=
      (isCompl_range_inl_inr A₀ Z).sup_eq_top
    rcases hcov.ge (Set.mem_univ p) with ⟨a, rfl⟩ | ⟨c, rfl⟩
    · have hpa : (g ≫ ιY).base a ∈ Ω := by
        rw [show (g ≫ ιY) a
            = (coprod.desc (g ≫ ιY) ιZ) ((coprod.inl : A₀ ⟶ A₀ ⨿ Z) a) from by
          rw [← Scheme.Hom.comp_apply, coprod.inl_desc]]
        exact hp
      refine isSquare_of_isSquare_map ((coprod.inl : A₀ ⟶ A₀ ⨿ Z).stalkMap a) ?_
      rw [Scheme.Hom.germ_stalkMap_apply (f := (coprod.inl : A₀ ⟶ A₀ ⨿ Z))
        (coprod.desc (g ≫ ιY) ιZ ⁻¹ᵁ Ω) a hp ((coprod.desc (g ≫ ιY) ιZ).app Ω u)]
      exact isSquare_germ_app_congr (coprod.inl_desc (g ≫ ιY) ιZ) u a hp hpa (hgsq a hpa)
    · exfalso
      have hmem : ιZ.base c ∈ (Ω : Set X)ᶜ := by
        rw [← hZrange]; exact Set.mem_range_self c
      refine hmem ?_
      rwa [← Scheme.Hom.comp_apply, coprod.inr_desc] at hp

/-- **(SQ).** For every scheme `X`, every point `x` of `X`, every open `Ω ∋ x` and every section
`u` of the structure sheaf over `Ω` there is a surjective integral morphism `f : A ⟶ X` such
that at every point `p` of `A` over `x` the image of `u` in the local ring of `A` at `p` is a
square.

This is the shape of the affine case
`Stacks.SquareRootCover.exists_isIntegralHom_surjective_isSquare_germ`, now for an arbitrary
base. -/
theorem exists_isIntegralHom_surjective_isSquare_germ_general (X : Scheme.{u}) (x : X)
    (Ω : X.Opens) (hx : x ∈ Ω) (u : Γ(X, Ω)) :
    ∃ (A : Scheme.{u}) (f : A ⟶ X), IsIntegralHom f ∧ Surjective f ∧
      ∀ (p : A) (hp : f.base p = x),
        IsSquare (A.presheaf.germ (f ⁻¹ᵁ Ω) p (show f.base p ∈ Ω from hp ▸ hx)
          (f.app Ω u)) := by
  obtain ⟨A, f, hint, hsurj, hsq⟩ :=
    exists_isIntegralHom_surjective_isSquare_germ_of_mem X Ω u
  exact ⟨A, f, hint, hsurj, fun p hp => hsq p _⟩

/-- **(SQ), in stalk-map form.** The same statement as
`Stacks.SquareRootCover.exists_isIntegralHom_surjective_isSquare_germ_general`, with the image
of `u` in the local ring of `A` at `p` written as the stalk map of `f` applied to the germ of
`u`; the two agree by `AlgebraicGeometry.Scheme.Hom.germ_stalkMap_apply`. -/
theorem exists_isIntegralHom_surjective_isSquare_stalkMap_general (X : Scheme.{u}) (x : X)
    (Ω : X.Opens) (hx : x ∈ Ω) (u : Γ(X, Ω)) :
    ∃ (A : Scheme.{u}) (f : A ⟶ X), IsIntegralHom f ∧ Surjective f ∧
      ∀ (p : A) (hp : f.base p = x),
        IsSquare (f.stalkMap p (X.presheaf.germ Ω (f.base p)
          (show f.base p ∈ Ω from hp ▸ hx) u)) := by
  obtain ⟨A, f, hint, hsurj, hsq⟩ :=
    exists_isIntegralHom_surjective_isSquare_germ_general X x Ω hx u
  refine ⟨A, f, hint, hsurj, fun p hp => ?_⟩
  rw [Scheme.Hom.germ_stalkMap_apply]
  exact hsq p hp

end Stacks.SquareRootCover

end
