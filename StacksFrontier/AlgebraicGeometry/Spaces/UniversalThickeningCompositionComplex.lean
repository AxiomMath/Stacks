module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleFactorizationVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.LocalCompleteIntersection.ConormalSequenceCompositionExact
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.BaseChangeOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalThickeningComposition

/-!
# Stacks 06BF at the source's hypotheses: clause (1) unconditionally, and the complex of clause (2)

`StacksFrontier/AlgebraicGeometry/Spaces/UniversalThickeningComposition.lean` constructs, for
morphisms `Z ⟶ Y ⟶ X` of algebraic spaces with universal first-order thickenings `Z ⊂ Z'` and
`Y ⊂ Y'` over `X`, the morphism `h : Z' ⟶ Y'`, proves that `Y ×_{Y'} Z'` is a universal
first-order thickening of `Z` over `Y` granted that the copy of `Z` inside it is a first-order
thickening, and proves exactness at the right term of the conormal sequence of clause (2).

This file removes the hypothesis of clause (1) and proves that the sequence of clause (2) is a
complex.

* **The square-zero condition inside the fibre product is derived.**  That the copy of `Z` is a
  *first-order* thickening of `Y ×_{Y'} Z'` is the inverse-image clause of Stacks 09ZX along the
  inclusion `Y ×_{Y'} Z' ⟶ Z'`, which `AlgebraicGeometry.Space.isFirstOrderThickening_preimage`
  carries for an arbitrary morphism of algebraic spaces; so it follows from `hZ` alone.
* **The sequence is a complex.**  The ambient morphism of the outer rectangle factors through
  `Y`, so it kills the defining ideal of `Y`, and the composite of the two maps of clause (2)
  vanishes.

## Main results

* `AlgebraicGeometry.Space.isUniversalFirstOrderThickening_comp'`: **Stacks 06BF, clause (1)**,
  with no hypothesis beyond the two universal first-order thickenings and `hfac`.
* `AlgebraicGeometry.Space.universalThickeningCompFibreInclusion_comp_map`: the ambient morphism
  of the outer rectangle factors through `Y`.
* `AlgebraicGeometry.Space.universalThickeningCompConormalMap_eq`: the left-hand map of
  clause (2) as a conormal map.
* `AlgebraicGeometry.Space.universalThickeningConormalMap_comp_conormalMap_eq_zero`:
  **Stacks 06BF, clause (2)**, the sequence is a complex.

## References

* [Stacks Project, Tag 06BF](https://stacks.math.columbia.edu/tag/06BF)
* [Stacks Project, Tag 09ZX](https://stacks.math.columbia.edu/tag/09ZX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Thickenings

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y' Z' : AlgebraicSpaces B S hS} {Y : Subfunctor Y'.obj} {Z : Subfunctor Z'.obj}
    {pY : Y' ⟶ X} {pZ : Z' ⟶ X} (i : Z.toFunctor ⟶ Y.toFunctor)
    (hZ : IsUniversalFirstOrderThickening B S hS Z pZ)
    (hY : IsUniversalFirstOrderThickening B S hS Y pY)
    (hfac : Z.ι ≫ pZ.hom = i ≫ Y.ι ≫ pY.hom)

/-! ### The lifting property of a fibre product of universal first-order thickenings -/

include hZ in
/-- The universal lifting property of the fibre product, in the form in which both clause (1)
of Stacks 06BF and its proof use it.  Let `Z ⊂ Z'` and `Y ⊂ Y'` be universal first-order
thickenings over `X`, let `h : Z' ⟶ Y'` restrict to `i : Z ⟶ Y` and lie over `X`, and let
`π : P ⟶ Y` exhibit `P` as the fibre product `Y ×_{Y'} Z'`, with second projection `κ` a
monomorphism.  Then `Z ×_{Z'} P ⊂ P` is a universal first-order thickening of `Z` over `Y`.

A morphism `T' ⟶ P` is a pair of morphisms to `Y` and to `Z'` agreeing over `Y'`.  The morphism
`e : T' ⟶ Z'` is the unique one furnished by the universal property of `Z ⊂ Z'` over `X`; that
`e ≫ h` agrees with the given `T' ⟶ Y ⟶ Y'` is uniqueness in the universal property of
`Y ⊂ Y'`, since both restrict to `Z ⟶ Y` on `T` and lie over `X`.

That `Z ×_{Z'} P ⊂ P` is a *first-order* thickening needs nothing of the fibre product: it is the
inverse image of the first-order thickening `Z ⊂ Z'` along `κ`, so Stacks 09ZX applies. -/
private theorem isUniversalFirstOrderThickening_of_isPullback'
    (h : Z' ⟶ Y') (hres : Z.ι ≫ h.hom = i ≫ Y.ι) (hover : h.hom ≫ pY.hom = pZ.hom)
    {P : AlgebraicSpaces B S hS}
    (π : P ⟶ (⟨Y.toFunctor, (IsNthOrderThickening.isThickening B S hS hY.firstOrder).1.1⟩ :
      AlgebraicSpaces B S hS))
    {κ : P.obj ⟶ Z'.obj} (hpb : IsPullback π.hom κ Y.ι h.hom) (hmono : Mono κ) :
    IsUniversalFirstOrderThickening B S hS (Z.preimage κ) π := by
  have hπι : π.hom ≫ Y.ι = κ ≫ h.hom := hpb.w
  have hζι : Z.fromPreimage κ ≫ Z.ι = (Z.preimage κ).ι ≫ κ := Subfunctor.fromPreimage_ι Z κ
  refine ⟨isFirstOrderThickening_preimage B S hS Z
    (ObjectProperty.homMk κ : P ⟶ Z') hZ.firstOrder, ?_⟩
  intro T' T hT a b hcompat
  -- The two morphisms `T' ⟶ Y'` agree, by uniqueness in the universal property of `Y ⊂ Y'`.
  have hb : T.ι ≫ b ≫ Y.ι = ((a ≫ Z.fromPreimage κ) ≫ i) ≫ Y.ι := by
    rw [← Category.assoc, hcompat]
    simp only [Category.assoc]
    rw [hπι, ← Category.assoc ((Z.preimage κ).ι), ← hζι]
    simp only [Category.assoc]
    rw [hres]
  have hcompatY : T.ι ≫ b ≫ Y.ι ≫ pY.hom =
      ((a ≫ Z.fromPreimage κ) ≫ i) ≫ Y.ι ≫ pY.hom := by
    simpa only [Category.assoc] using hb =≫ pY.hom
  -- Push the solid diagram into `Z'` and lift it by universality of `Z ⊂ Z'` over `X`.
  have hcompatZ : T.ι ≫ b ≫ Y.ι ≫ pY.hom = (a ≫ Z.fromPreimage κ) ≫ Z.ι ≫ pZ.hom := by
    rw [hcompatY, ← hover]
    simp only [Category.assoc, reassoc_of% hres]
  obtain ⟨e, he, heu⟩ := hZ.existsUnique_lift T hT (a ≫ Z.fromPreimage κ)
    (b ≫ Y.ι ≫ pY.hom) hcompatZ
  obtain ⟨y₀, -, hyu⟩ := hY.existsUnique_lift T hT ((a ≫ Z.fromPreimage κ) ≫ i)
    (b ≫ Y.ι ≫ pY.hom) hcompatY
  have hagree : b ≫ Y.ι = e ≫ h.hom := by
    refine (hyu (b ≫ Y.ι) ⟨hb, by simp only [Category.assoc]⟩).trans
      (hyu (e ≫ h.hom) ⟨?_, ?_⟩).symm
    · rw [← Category.assoc, he.1]
      simp only [Category.assoc]
      rw [hres]
    · rw [Category.assoc, hover]
      exact he.2
  -- Assemble the lift from the mapping property of the fibre product.
  refine ⟨hpb.lift b e hagree, ⟨?_, hpb.lift_fst b e hagree⟩, ?_⟩
  · refine (cancel_mono κ).mp ?_
    rw [Category.assoc, hpb.lift_snd, he.1]
    simp only [Category.assoc]
    rw [hζι]
  · intro c hc
    refine (cancel_mono κ).mp ?_
    rw [hpb.lift_snd]
    refine heu (c ≫ κ) ⟨?_, ?_⟩
    · rw [← Category.assoc, hc.1]
      simp only [Category.assoc]
      rw [← hζι]
    · rw [Category.assoc, ← hover, ← Category.assoc κ, ← hπι]
      simp only [Category.assoc]
      rw [← Category.assoc c π.hom, hc.2]

include hfac

/-! ### Clause (1): the fibre product is the universal first-order thickening over `Y` -/

/-- **Stacks 06BF, clause (1), the universal first-order thickening of `Z` over `Y`.**  With the
morphism `h : Z' ⟶ Y'` of `AlgebraicGeometry.Space.universalThickeningCompMap`, the fibre
product `Y ×_{Y'} Z'` is a universal first-order thickening of `Z` over `Y`, with structure
morphism the projection to `Y`.

A morphism `T' ⟶ Y ×_{Y'} Z'` is a pair of morphisms to `Y` and to `Z'` agreeing over `Y'`.
Given a solid diagram over `Y` built from a first-order thickening `T ⊂ T'` and a morphism
`T ⟶ Z`, the morphism to `Y` is the one the diagram supplies and the morphism `e : T' ⟶ Z'` is
the unique one furnished by the universal property of `Z ⊂ Z'` over `X`.  That the two agree
over `Y'` is uniqueness in the universal property of `Y ⊂ Y'`: both composites restrict to
`Z ⟶ Y` on `T` and lie over `X`, the first because `h` restricts to `i` and lies over `X`.
Uniqueness of the resulting morphism is uniqueness of `e` together with the fact that the
inclusion of the fibre product into `Z'` is a monomorphism.

That the copy of `Z` is a first-order thickening of `Y ×_{Y'} Z'` needs nothing of the fibre
product: it is the inverse image of `Z ⊂ Z'` along the inclusion `Y ×_{Y'} Z' ⟶ Z'`, so it is
one by the inverse-image clause of Stacks 09ZX,
`AlgebraicGeometry.Space.isFirstOrderThickening_preimage`. -/
@[stacks 06BF "clause (1): Y ×_{Y'} Z' is the universal first-order thickening of Z over Y"]
theorem isUniversalFirstOrderThickening_comp' :
    IsUniversalFirstOrderThickening B S hS
      (universalThickeningCompSub B S hS i hZ hY hfac)
      (universalThickeningCompStructure B S hS i hZ hY hfac) :=
  isUniversalFirstOrderThickening_of_isPullback' B S hS i hZ hY
    (universalThickeningCompMap B S hS i hZ hY hfac)
    (universalThickeningCompMap_restrict B S hS i hZ hY hfac)
    (universalThickeningCompMap_over_hom B S hS i hZ hY hfac)
    (universalThickeningCompStructure B S hS i hZ hY hfac)
    (Subfunctor.isPullback_preimage
      (universalThickeningCompMap B S hS i hZ hY hfac).hom Y)
    inferInstance

/-! ### Clause (2): the sequence is a complex -/

/-- **The ambient morphism of the outer rectangle factors through `Y`.**  The inclusion of the
fibre product `Y ×_{Y'} Z'` into `Z'` followed by `h : Z' ⟶ Y'` is the projection to `Y`
followed by the inclusion `Y ⟶ Y'`.

This is `CategoryTheory.Subfunctor.fromPreimage_ι` read in the category of algebraic spaces, the
fibre product being the inverse image `h⁻¹(Y)`; it is the factorization that makes the composite
of the two maps of clause (2) vanish. -/
theorem universalThickeningCompFibreInclusion_comp_map :
    universalThickeningCompFibreInclusion B S hS i hZ hY hfac ≫
        universalThickeningCompMap B S hS i hZ hY hfac =
      universalThickeningCompStructure B S hS i hZ hY hfac ≫
        subspaceInclusion B S hS Y'
          ⟨Y, (IsNthOrderThickening.isThickening B S hS hY.firstOrder).1⟩ := by
  apply ObjectProperty.hom_ext
  exact (Subfunctor.fromPreimage_ι Y
    (universalThickeningCompMap B S hS i hZ hY hfac).hom).symm

/-- **The left-hand map of clause (2) is the conormal map of Stacks 04CP of the square of closed
subspaces it is built from.**  The two are the same morphism by definition.  The identification
is stated on the two morphisms alone, and not under the inverse image of modules that the
composite below applies to them, because that is what keeps the definitional comparison out of a
composition; see the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleBaseChangeEpi.lean`. -/
theorem universalThickeningCompConormalMap_eq :
    universalThickeningConormalMap B S hS (𝟙 X : X ⟶ X) i hZ hY
        (universalThickeningComp_square B S hS i hfac) =
      conormalMap B S hS ⟨Z, (IsNthOrderThickening.isThickening B S hS hZ.firstOrder).1⟩
        ⟨Y, (IsNthOrderThickening.isThickening B S hS hY.firstOrder).1⟩
        (universalThickeningCompMap B S hS i hZ hY hfac)
        (ObjectProperty.homMk i)
        (universalThickeningComp_subspace_square B S hS i hZ hY hfac) :=
  rfl

/-- **Stacks 06BF, clause (2): the sequence is a complex.**  The composite of the two maps
`i^*𝒞_{Y/X} ⟶ 𝒞_{Z/X} ⟶ 𝒞_{Z/Y}` of the conormal sequence of the composition is zero.

The left-hand map is the inverse image, along the projection of the copy of `Z` inside
`Y ×_{Y'} Z'`, of the canonical map of Stacks 060A at the square of
`AlgebraicGeometry.Space.universalThickeningComp_square`, and the right-hand map is the map of
Stacks 04CP for the inclusion `Y ×_{Y'} Z' ⟶ Z'`.  So the composite is the conormal map of the
outer rectangle of those two stacked squares, by part (3) of Stacks 04G2, and the ambient
morphism of that rectangle is `Y ×_{Y'} Z' ⟶ Z' ⟶ Y'`, which factors through the inclusion of
`Y` by `AlgebraicGeometry.Space.universalThickeningCompFibreInclusion_comp_map`.  A conormal map
whose ambient morphism factors through the lower closed subspace is zero, the defining ideal of
that subspace being the kernel of the comorphism of its inclusion; that is
`AlgebraicGeometry.Space.comp_conormalMap_eq_zero_of_factors`.

The left-hand map is written here as that map of Stacks 04CP rather than as
`AlgebraicGeometry.Space.universalThickeningConormalMap`; the two are the same morphism, by
`AlgebraicGeometry.Space.universalThickeningCompConormalMap_eq`.  Writing it the second way makes
the statement one the kernel cannot check: the definitional comparison would then sit inside the
inverse image of modules and inside a composition, which is exactly what the implementation notes
of `StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleBaseChangeEpi.lean` record as beyond the
budget.

A consumer wanting the arrows of this sequence should take them from *this* theorem, as
`CategoryTheory.ShortComplex.f` and `CategoryTheory.ShortComplex.g` of
`CategoryTheory.ShortComplex.mk _ _` applied to it, which is what
`AlgebraicGeometry.Space.universalThickeningCompConormalSequence_shortExact'`, Stacks 06CC, does.
Crossing the two spellings by rewriting with
`AlgebraicGeometry.Space.universalThickeningCompConormalMap_eq` is *not* an available route once
the arrow sits under the inverse image of modules, and neither is naming either arrow in a
definition of its own — the section *How the sequence is written* of the file of that theorem
records what each of those costs. -/
@[stacks 06BF "clause (2): the sequence is a complex, the composite of i^*𝒞_{Y/X} ⟶ 𝒞_{Z/X} and \
𝒞_{Z/X} ⟶ 𝒞_{Z/Y} being zero"]
theorem universalThickeningConormalMap_comp_conormalMap_eq_zero :
    (modulePullback B S hS
          (preimageProjection B S hS
            (universalThickeningCompFibreInclusion B S hS i hZ hY hfac)
            ⟨Z, (IsNthOrderThickening.isThickening B S hS hZ.firstOrder).1⟩)).map
        (conormalMap B S hS ⟨Z, (IsNthOrderThickening.isThickening B S hS hZ.firstOrder).1⟩
          ⟨Y, (IsNthOrderThickening.isThickening B S hS hY.firstOrder).1⟩
          (universalThickeningCompMap B S hS i hZ hY hfac)
          (ObjectProperty.homMk i)
          (universalThickeningComp_subspace_square B S hS i hZ hY hfac)) ≫
      conormalMap B S hS
        (preimageSubspace B S hS
          (universalThickeningCompFibreInclusion B S hS i hZ hY hfac)
          ⟨Z, (IsNthOrderThickening.isThickening B S hS hZ.firstOrder).1⟩)
        ⟨Z, (IsNthOrderThickening.isThickening B S hS hZ.firstOrder).1⟩
        (universalThickeningCompFibreInclusion B S hS i hZ hY hfac)
        (preimageProjection B S hS
          (universalThickeningCompFibreInclusion B S hS i hZ hY hfac)
          ⟨Z, (IsNthOrderThickening.isThickening B S hS hZ.firstOrder).1⟩)
        (conormalEtaleRestrictionSquare B S hS
          (universalThickeningCompFibreInclusion B S hS i hZ hY hfac)
          ⟨Z, (IsNthOrderThickening.isThickening B S hS hZ.firstOrder).1⟩) = 0 := by
  have key := comp_conormalMap_eq_zero_of_factors B S hS
    (universalThickeningCompFibreInclusion B S hS i hZ hY hfac)
    (universalThickeningCompMap B S hS i hZ hY hfac)
    (preimageSubspace B S hS
      (universalThickeningCompFibreInclusion B S hS i hZ hY hfac)
      ⟨Z, (IsNthOrderThickening.isThickening B S hS hZ.firstOrder).1⟩)
    ⟨Z, (IsNthOrderThickening.isThickening B S hS hZ.firstOrder).1⟩
    ⟨Y, (IsNthOrderThickening.isThickening B S hS hY.firstOrder).1⟩
    (preimageProjection B S hS
      (universalThickeningCompFibreInclusion B S hS i hZ hY hfac)
      ⟨Z, (IsNthOrderThickening.isThickening B S hS hZ.firstOrder).1⟩)
    (ObjectProperty.homMk i)
    (conormalEtaleRestrictionSquare B S hS
      (universalThickeningCompFibreInclusion B S hS i hZ hY hfac)
      ⟨Z, (IsNthOrderThickening.isThickening B S hS hZ.firstOrder).1⟩)
    (universalThickeningComp_subspace_square B S hS i hZ hY hfac)
    (universalThickeningCompStructure B S hS i hZ hY hfac)
    (universalThickeningCompFibreInclusion_comp_map B S hS i hZ hY hfac)
  rw [key]

end AlgebraicGeometry.Space

end
