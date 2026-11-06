module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AffineEquivalence
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.Abelian

/-!
# The affine-section functor is exact on the adequate modules

Over an affine base `U = Spec A` the comparison functor `𝓕 ↦ F_{𝓕, A}` of [Stacks, Tag 06ZJ]
from `Adeq(𝒪)` to the adequate module-valued functors on the `A`-algebras of the site is an
**equivalence of categories**, `Stacks.Adequate.isEquivalence_adequateComparison`, with no
hypothesis. An equivalence preserves all limits and colimits, and the inclusion of the adequate
functors into all module-valued functors preserves kernels and cokernels, adequacy on the
algebras of the site being closed under both ([Stacks, Tags 06V3 and 06V2] there, which are the
theorems `Stacks.Adequate.affineAdequateKernels` and
`Stacks.Adequate.affineAdequateCokernels`). Since
`Stacks.Adequate.adequateComparison_ι` identifies the composite of the comparison with those
two inclusions as the affine-section functor, the affine-section functor is **exact** on
`Adeq(𝒪)`, and that is what this module records.

## Main results

* `Stacks.Adequate.adequateOn_isClosedUnderKernels` and
  `Stacks.Adequate.adequateOn_isClosedUnderCokernels` — adequacy of module-valued functors on
  the `A`-algebras of a chosen big site over `Spec A` is closed under kernels and cokernels.
  These are [Stacks, Tags 06V3 and 06V2] on that domain of algebras, packaged as the closure
  properties `CategoryTheory.ObjectProperty.IsClosedUnderKernels` and
  `CategoryTheory.ObjectProperty.IsClosedUnderCokernels` that the abelian structure of the
  subcategory and the exactness of its inclusion consume.
* `Stacks.Adequate.preservesFiniteLimits_affineSections` and
  `Stacks.Adequate.preservesFiniteColimits_affineSections` — **the affine-section functor of a
  chosen big site over an affine base is exact on the adequate `𝒪`-modules**, with no
  hypothesis.
* `Stacks.Adequate.preservesHomology_affineSections` — the same exactness in the form the
  homotopy-category machinery consumes.
* `Stacks.Adequate.reflectsIsomorphisms_affineSections` — it also reflects isomorphisms.
* `Stacks.Adequate.plus_subcategoryAcyclic_eq_inverseImage` — for *any* additive functor between
  abelian categories which preserves homology and reflects isomorphisms, the acyclic complexes
  of the bounded below homotopy category are the inverse image of the acyclic complexes. This is
  the shape in which the remaining hypothesis of [Stacks, Tag 06ZR] asks for an identification
  of acyclic complexes, and the three properties it wants of the functor are exactly the three
  the affine-section functor has above.

## Implementation notes

**Why this is not the route of the source.** The source reads the exactness of sections over an
affine object off the vanishing of the higher cohomology of an adequate module there, which is
[Stacks, Tag 06VM] (3). In this library that vanishing is
`Stacks.Adequate.BigSite.isZero_rightDerived_sections_of_isAdequate`, which lies above this
module in the import order. The route taken here does not need it:
it reads exactness off the *equivalence* of [Stacks, Tag 06ZJ], which is unconditional, and
off the two closure properties of adequacy on the algebras of the site that are theorems. In
particular it avoids `Stacks.Adequate.AffineAdequateExtensions` and
`Stacks.Adequate.AffineAdequateColimits`, the two closure properties the library does not have.

**The universe.** `Stacks.Adequate.isEquivalence_adequateComparison` is proved at `.{u, u}`,
its essential surjectivity producing the adequate `𝒪`-module as a kernel of associated modules
through `AlgebraicGeometry.tilde`, which takes a `ModuleCat.{u} A`. So the results here are at
`.{u, u}` as well; the universe arguments are written out because `max u ?m =?= u` is not
solvable by unification.

**`rw` rather than `exact`.** `Stacks.Adequate.adequateComparison_ι` is an *equality* of
functors, proved by `rfl`, so the goal is rewritten along it rather than transported along an
isomorphism; nothing has to be moved across an `eqToHom`.

## References

* [Stacks Project, Tag 06ZJ](https://stacks.math.columbia.edu/tag/06ZJ)
* [Stacks Project, Tag 06VQ](https://stacks.math.columbia.edu/tag/06VQ)
* [Stacks Project, Tag 06V3](https://stacks.math.columbia.edu/tag/06V3)
* [Stacks Project, Tag 06V2](https://stacks.math.columbia.edu/tag/06V2)
* [Stacks Project, Tag 06VM](https://stacks.math.columbia.edu/tag/06VM)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Adequate

variable {τ : CoveringTopology} {A : CommRingCat.{u}} (B : BigSite τ (Spec A))

/-! ### Closure of adequacy on the algebras of the site -/

/-- Adequacy of module-valued functors on the `A`-algebras of a chosen big site over `Spec A`
is closed under kernels: this is [Stacks, Tag 06V3] on that domain of algebras, which is the
theorem `Stacks.Adequate.affineAdequateKernels`, packaged as the closure property the abelian
structure of the subcategory consumes. -/
public theorem adequateOn_isClosedUnderKernels :
    ObjectProperty.IsClosedUnderKernels
      (adequateOn.{u, u} A (schemeSizeBelow B.cutoff)) where
  kernels_le := by
    rintro _ ⟨φ, k, hk, hF, hG⟩
    exact (adequateOn.{u, u} A (schemeSizeBelow B.cutoff)).prop_of_iso
      (IsLimit.conePointUniqueUpToIso (limit.isLimit (parallelPair φ 0)) hk)
      (affineAdequateKernels.{u, u} B A B.base_mem φ hF hG)

/-- Adequacy of module-valued functors on the `A`-algebras of a chosen big site over `Spec A`
is closed under cokernels: this is [Stacks, Tag 06V2] on that domain of algebras, which is the
theorem `Stacks.Adequate.affineAdequateCokernels`. -/
public theorem adequateOn_isClosedUnderCokernels :
    ObjectProperty.IsClosedUnderCokernels
      (adequateOn.{u, u} A (schemeSizeBelow B.cutoff)) where
  cokernels_le := by
    rintro _ ⟨φ, k, hk, hF, hG⟩
    exact (adequateOn.{u, u} A (schemeSizeBelow B.cutoff)).prop_of_iso
      (IsColimit.coconePointUniqueUpToIso (colimit.isColimit (parallelPair φ 0)) hk)
      (affineAdequateCokernels.{u, u} B A B.base_mem φ hF hG)

/-! ### Exactness of the affine-section functor on the adequate modules -/

/-- **The affine-section functor is left exact on the adequate `𝒪`-modules**, with no
hypothesis: it is the equivalence of [Stacks, Tag 06ZJ] followed by the inclusion of the
adequate module-valued functors, and that inclusion preserves kernels. -/
public theorem preservesFiniteLimits_affineSections :
    PreservesFiniteLimits ((adequate.{u, u} B).ι ⋙
      affineSectionsFunctor B A (𝟙 (Spec A))) := by
  let := adequateOn_isClosedUnderKernels B
  let := adequateOn_isClosedUnderCokernels B
  let := isEquivalence_adequateComparison B
  rw [← adequateComparison_ι.{u, u} B]
  have : PreservesFiniteLimits (adequateOn.{u, u} A (schemeSizeBelow B.cutoff)).ι :=
    have := (adequateOn.{u, u} A (schemeSizeBelow B.cutoff)).preservesKernels_ι
    Functor.preservesFiniteLimits_of_preservesKernels _
  exact comp_preservesFiniteLimits _ _

/-- **The affine-section functor is right exact on the adequate `𝒪`-modules**, with no
hypothesis: it is the equivalence of [Stacks, Tag 06ZJ] followed by the inclusion of the
adequate module-valued functors, and that inclusion preserves cokernels.

This is the assertion the source obtains from [Stacks, Tag 06VM] (3), the vanishing of the
higher cohomology of an adequate module on an affine object; see the module documentation for
why the equivalence is used instead. -/
public theorem preservesFiniteColimits_affineSections :
    PreservesFiniteColimits ((adequate.{u, u} B).ι ⋙
      affineSectionsFunctor B A (𝟙 (Spec A))) := by
  let := adequateOn_isClosedUnderKernels B
  let := adequateOn_isClosedUnderCokernels B
  let := isEquivalence_adequateComparison B
  rw [← adequateComparison_ι.{u, u} B]
  have : PreservesFiniteColimits (adequateOn.{u, u} A (schemeSizeBelow B.cutoff)).ι :=
    have := (adequateOn.{u, u} A (schemeSizeBelow B.cutoff)).preservesCokernels_ι
    have : HasFiniteProducts (adequateOn.{u, u} A (schemeSizeBelow B.cutoff)).FullSubcategory :=
      inferInstance
    have : HasFiniteBiproducts (adequateOn.{u, u} A (schemeSizeBelow B.cutoff)).FullSubcategory :=
      HasFiniteBiproducts.of_hasFiniteProducts
    have : HasFiniteCoproducts (adequateOn.{u, u} A (schemeSizeBelow B.cutoff)).FullSubcategory :=
      hasFiniteCoproducts_of_hasFiniteBiproducts _
    Functor.preservesFiniteColimits_of_preservesCokernels _
  exact comp_preservesFiniteColimits _ _

/-- **The affine-section functor preserves homology on the adequate `𝒪`-modules**: it preserves
kernels and cokernels, which is
`Stacks.Adequate.preservesFiniteLimits_affineSections` and
`Stacks.Adequate.preservesFiniteColimits_affineSections`. This is the exactness in the form the
homotopy-category machinery consumes. -/
public theorem preservesHomology_affineSections :
    ((adequate.{u, u} B).ι ⋙
      affineSectionsFunctor B A (𝟙 (Spec A))).PreservesHomology :=
  have := preservesFiniteLimits_affineSections B
  have := preservesFiniteColimits_affineSections B
  { preservesKernels _ := inferInstance
    preservesCokernels _ := inferInstance }

/-- **The affine-section functor reflects isomorphisms on the adequate `𝒪`-modules**: it is the
equivalence of [Stacks, Tag 06ZJ] followed by a fully faithful inclusion. -/
public theorem reflectsIsomorphisms_affineSections :
    ((adequate.{u, u} B).ι ⋙
      affineSectionsFunctor B A (𝟙 (Spec A))).ReflectsIsomorphisms := by
  let := isEquivalence_adequateComparison B
  rw [← adequateComparison_ι.{u, u} B]
  have h₁ : (adequateComparison.{u, u} B).ReflectsIsomorphisms :=
    (Functor.FullyFaithful.ofFullyFaithful (adequateComparison.{u, u} B)).reflectsIsomorphisms
  have h₂ : (adequateOn.{u, u} A (schemeSizeBelow B.cutoff)).ι.ReflectsIsomorphisms :=
    (adequateOn.{u, u} A (schemeSizeBelow B.cutoff)).fullyFaithfulι.reflectsIsomorphisms
  exact reflectsIsomorphisms_comp _ _

/-! ### Acyclicity across an exact functor that reflects isomorphisms -/

section Reflect

variable {C D : Type*} [Category* C] [Category* D]

/-- An additive functor that reflects isomorphisms reflects zero objects: `F X` being zero makes
the zero endomorphism of `F X` an isomorphism, and `F` carries the zero endomorphism of `X` to
it. -/
public theorem isZero_of_isZero_map [Preadditive C] [Preadditive D]
    (F : C ⥤ D) [F.Additive] [F.ReflectsIsomorphisms] {X : C} (h : IsZero (F.obj X)) :
    IsZero X := by
  have h₁ : IsIso (F.map (0 : X ⟶ X)) := by
    rw [F.map_zero, ← (IsZero.iff_id_eq_zero _).mp h]
    infer_instance
  have h₂ := isIso_of_reflects_iso (0 : X ⟶ X) F
  rw [IsZero.iff_id_eq_zero, ← IsIso.hom_inv_id (0 : X ⟶ X), zero_comp]

/-- **An exact functor that reflects isomorphisms detects acyclicity.** For `F` additive,
preserving homology and reflecting isomorphisms, a cochain complex is acyclic exactly when its
image is: homology commutes with `F` by `CategoryTheory.ShortComplex.mapHomologyIso`, and `F`
reflects the vanishing of a homology object by
`Stacks.Adequate.isZero_of_isZero_map`. -/
public theorem acyclic_map_iff [Abelian C] [Abelian D]
    (F : C ⥤ D) [F.Additive] [F.PreservesHomology] [F.ReflectsIsomorphisms]
    (K : CochainComplex C ℤ) :
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).Acyclic ↔ K.Acyclic := by
  refine forall_congr' fun n ↦ ?_
  rw [HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff_isZero_homology]
  exact ⟨fun h ↦ isZero_of_isZero_map F (h.of_iso ((K.sc n).mapHomologyIso F).symm),
    fun h ↦ (F.map_isZero h).of_iso ((K.sc n).mapHomologyIso F)⟩

/-- `Stacks.Adequate.acyclic_map_iff` in the bounded below homotopy category. -/
public theorem plus_acyclic_map_iff [Abelian C] [Abelian D]
    (F : C ⥤ D) [F.Additive] [F.PreservesHomology] [F.ReflectsIsomorphisms]
    (K : HomotopyCategory.Plus C) :
    HomotopyCategory.Plus.subcategoryAcyclic D (F.mapHomotopyCategoryPlus.obj K) ↔
      HomotopyCategory.Plus.subcategoryAcyclic C K := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.Plus.quotient_obj_surjective K
  show HomotopyCategory.subcategoryAcyclic D
      ((HomotopyCategory.quotient D _).obj ((F.mapHomologicalComplex _).obj K.obj)) ↔
    HomotopyCategory.subcategoryAcyclic C ((HomotopyCategory.quotient C _).obj K.obj)
  rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic,
    HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic]
  exact acyclic_map_iff F K.obj

/-- **The acyclic complexes are the inverse image of the acyclic complexes along an exact
functor that reflects isomorphisms.** This is the shape in which the hypothesis `hacyc` of
`Stacks.Adequate.BigSite.isLocalization_mapHomotopyCategoryPlus_associatedModuleAdeq_of_acyclic`
asks for an identification of acyclic complexes. -/
public theorem plus_subcategoryAcyclic_eq_inverseImage [Abelian C] [Abelian D]
    (F : C ⥤ D) [F.Additive] [F.PreservesHomology] [F.ReflectsIsomorphisms] :
    HomotopyCategory.Plus.subcategoryAcyclic C =
      (HomotopyCategory.Plus.subcategoryAcyclic D).inverseImage
        F.mapHomotopyCategoryPlus := by
  ext K
  exact (plus_acyclic_map_iff F K).symm

end Reflect

end Stacks.Adequate

end
