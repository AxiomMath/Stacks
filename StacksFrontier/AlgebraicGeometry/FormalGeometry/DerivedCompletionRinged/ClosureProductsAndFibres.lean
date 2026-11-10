module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.CompleteShift
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.DerivedLimits
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.VanishingIdealSheafRestriction
import all StacksFrontier.AlgebraicGeometry.ProEtale.DerivedCompleteInverseLimit

/-!
# Derived-complete objects of `D(𝒪)` are closed under countable products and mapping fibres

Let `(𝒞, 𝒪)` be a ringed site and `ℐ ⊆ 𝒪` a sheaf of ideals. The derived-completeness predicate
`AlgebraicGeometry.RingedSite.IsDerivedComplete` of [Stacks, Tag 0999] tests, at every object
`U` of the site and every section `f ∈ ℐ(U)`, the invertibility of the Milnor difference
`1 - f·shift` on the countable product of copies of `K|_U` in `D(𝒪_U)`. This file shows that the
objects satisfying it are closed under the countable products of `D(𝒪)` and satisfy
two-out-of-three along a distinguished triangle, and deduces that a derived limit of a tower of
derived-complete objects is derived complete.

## Main results

* `AlgebraicGeometry.RingedSite.isDerivedComplete_pi`: **a countable product of
  derived-complete objects is derived complete.**
* `AlgebraicGeometry.RingedSite.isDerivedComplete_of_distTriang`: **two-out-of-three** — if the
  second and third objects of a distinguished triangle of `D(𝒪)` are derived complete, so is the
  first. This is the closure under mapping fibres: the fibre of a morphism is the first object of
  a distinguished triangle whose other two objects are its source and target.
* `AlgebraicGeometry.RingedSite.exists_isDerivedComplete_fibre`: the same statement read off a
  morphism — a morphism of derived-complete objects has a derived-complete mapping fibre.
* `AlgebraicGeometry.RingedSite.isDerivedComplete_of_isDerivedLimit`: **a derived limit of a
  tower of derived-complete objects is derived complete**, which is the two results above
  combined along the Milnor triangle of the tower.

The sectionwise statements `AlgebraicGeometry.RingedSite.IsDerivedCompleteAtSection.pi` and
`AlgebraicGeometry.RingedSite.IsDerivedCompleteAtSection.of_distTriang` carry the content; the
four results above are those conditions quantified over the local sections of `ℐ` through
`AlgebraicGeometry.RingedSite.isDerivedComplete_iff_forall_isDerivedCompleteAtSection`.

## Implementation notes

Both halves are formal consequences of the corresponding statements for a single scalar in a
linear category, `isDerivedCompleteAt_pi` and `isDerivedCompleteAt_of_distTriang` of
`StacksFrontier/Homology/DerivedComplete.lean`, applied in the derived category of the slice site at
`U` — *provided* the restriction `D(𝒪) ⥤ D(𝒪_U)` carries the relevant structure there.

For the triangle that is immediate: restriction of sheaves of modules to a slice site is exact,
so `CategoryTheory.Functor.mapDerivedCategory` of it is a triangulated functor and carries a
distinguished triangle to one.

For the product it is not. The countable products of `D(𝒪)` do not commute with restriction for
any formal reason: they are not computed termwise, Grothendieck's axiom AB4\* failing for sheaves
of modules, and come instead from K-injective resolutions
(`Stacks.KInjectiveProducts.hasProductsOfShape_derivedCategory_sheafOfModules`). What makes the
product case go through is
`AlgebraicGeometry.RingedSite.preservesProducts_mapDerivedCategory_overFunctor` of
`VanishingIdealSheafRestriction.lean` (in this directory), which says the restriction *does*
preserve them, by the K-injective route: restriction has extension by zero as a left adjoint,
hence preserves products of sheaves of modules, and it carries K-injective complexes to
K-injective complexes by [Stacks, Tag 08FI].

That is what fixes the universes. The product preservation is available for a
`RingedSite.{u, u, u}` with sheaves of modules in the same universe `u`, which is the
specialization at `v = w = u` of the generality in which the predicate is stated, and the
generality of the other ringed-site results about derived completeness — among them
[Stacks, Tag 0998] and the first assertion of [Stacks, Tag 0CQH].

The derived category model is `HasDerivedCategory.standard`, installed as a file-level local
instance because the predicate is defined at it.

No `@[stacks]` attribute is attached. [Stacks, Tag 0999] is carried by the predicate itself, and
the closure properties here are the unlabelled first half of the sentence of [Stacks, Tag 099C]
that the subcategory of derived-complete objects is a triangulated subcategory closed under
products; the tag is carried elsewhere for its inverse-image assertion.

## References

* [Stacks Project, Tag 0999](https://stacks.math.columbia.edu/tag/0999)
* [Stacks Project, Tag 08FI](https://stacks.math.columbia.edu/tag/08FI)
* [Stacks Project, Tag 091W](https://stacks.math.columbia.edu/tag/091W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open scoped IsMulCommutative

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u})

attribute [local instance] isMulCommutative_over overCatCenterLinear
  overFunctor_preservesFiniteLimits overFunctor_preservesFiniteColimits
  hasProductsOfShape_nat_derivedCategory_over hasProductsOfShape_nat_derivedCategory_ringSheaf

/-- **The condition `T(K|_U, f) = 0` is stable under countable products.** For a countable family
of objects of `D(𝒪)` each of whose restrictions to the slice site at `U` is derived complete at
the section `f`, the restriction of their product is derived complete at `f`.

The product of `D(𝒪)` is not computed termwise, so this is not formal: it rests on
`preservesProducts_mapDerivedCategory_overFunctor`, which says that restriction to the slice site
nonetheless commutes with the countable products of the derived categories. Given that, the
restriction of the product is the product of the restrictions, and `isDerivedCompleteAt_pi`
applies in `D(𝒪_U)`. -/
theorem IsDerivedCompleteAtSection.pi
    (K : ℕ →
      DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (U : X.C) (f : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj.obj (op U))
    (hK : ∀ n, IsDerivedCompleteAtSection X (K n) U f) :
    IsDerivedCompleteAtSection X (∏ᶜ K) U f := by
  have := preservesProducts_mapDerivedCategory_overFunctor X U
  exact (isDerivedCompleteAt_iff_of_iso
    (PreservesProduct.iso
      (SheafOfModules.overFunctor.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).mapDerivedCategory K)
    (overTerminalRingHom X U f)).2 (isDerivedCompleteAt_pi hK)

/-- **The condition `T(K|_U, f) = 0` satisfies two-out-of-three along a distinguished triangle.**
Restriction of sheaves of modules to the slice site at `U` is exact, so the functor it induces on
derived categories is triangulated and carries the triangle to a distinguished triangle of
`D(𝒪_U)`; `isDerivedCompleteAt_of_distTriang` then gives the first object from the second and the
third. -/
theorem IsDerivedCompleteAtSection.of_distTriang
    {T : Triangle
      (DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))}
    (hT : T ∈ distTriang
      (DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))))
    (U : X.C) (f : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj.obj (op U))
    (h₂ : IsDerivedCompleteAtSection X T.obj₂ U f)
    (h₃ : IsDerivedCompleteAtSection X T.obj₃ U f) :
    IsDerivedCompleteAtSection X T.obj₁ U f :=
  AlgebraicGeometry.RingedSite.isDerivedCompleteAt_of_distTriang
    ((SheafOfModules.overFunctor.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).mapDerivedCategory.map_distinguished
      T hT)
    h₂ h₃

variable (I : SheafOfModules.Submodule
  (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))

/-- **A countable product of derived-complete objects of `D(𝒪)` is derived complete.**

Derived completeness is a condition on the restriction of the object to every slice site, and
restriction commutes with the countable products of the derived categories
(`preservesProducts_mapDerivedCategory_overFunctor`), so the condition passes to the product by
`isDerivedCompleteAt_pi`. -/
theorem isDerivedComplete_pi
    (K : ℕ → DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (hK : ∀ n, IsDerivedComplete.{u, u, u, u} X I (K n)) :
    IsDerivedComplete.{u, u, u, u} X I (∏ᶜ K) :=
  (isDerivedComplete_iff_forall_isDerivedCompleteAtSection X _ I).2 fun U f hf ↦
    IsDerivedCompleteAtSection.pi X K U f fun n ↦
      (isDerivedComplete_iff_forall_isDerivedCompleteAtSection X _ I).1 (hK n) U f hf

/-- **Two-out-of-three for derived completeness along a distinguished triangle of `D(𝒪)`**: if
the second and third objects of a distinguished triangle are derived complete along `ℐ`, then so
is the first.

This is the closure of the derived-complete objects under mapping fibres: the fibre of a morphism
`φ` is the first object of a distinguished triangle whose second and third objects are the source
and the target of `φ`. -/
theorem isDerivedComplete_of_distTriang
    {T : Triangle
      (DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))}
    (hT : T ∈ distTriang
      (DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))))
    (h₂ : IsDerivedComplete.{u, u, u, u} X I T.obj₂)
    (h₃ : IsDerivedComplete.{u, u, u, u} X I T.obj₃) :
    IsDerivedComplete.{u, u, u, u} X I T.obj₁ :=
  (isDerivedComplete_iff_forall_isDerivedCompleteAtSection X _ I).2 fun U f hf ↦
    IsDerivedCompleteAtSection.of_distTriang X hT U f
      ((isDerivedComplete_iff_forall_isDerivedCompleteAtSection X _ I).1 h₂ U f hf)
      ((isDerivedComplete_iff_forall_isDerivedCompleteAtSection X _ I).1 h₃ U f hf)

/-- **A morphism of derived-complete objects of `D(𝒪)` has a derived-complete mapping fibre.**
Completing `φ` to a distinguished triangle on the left, the fibre is the first object of a
distinguished triangle whose second and third objects are `A` and `B`, so
`isDerivedComplete_of_distTriang` applies to it. -/
theorem exists_isDerivedComplete_fibre
    {A B : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))}
    (φ : A ⟶ B)
    (hA : IsDerivedComplete.{u, u, u, u} X I A)
    (hB : IsDerivedComplete.{u, u, u, u} X I B) :
    ∃ (Z : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
      (ι : Z ⟶ A) (δ : B ⟶ Z⟦(1 : ℤ)⟧),
      Triangle.mk ι φ δ ∈
        distTriang
          (DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) ∧
        IsDerivedComplete.{u, u, u, u} X I Z := by
  obtain ⟨Z, ι, δ, hT⟩ := distinguished_cocone_triangle₁ φ
  exact ⟨Z, ι, δ, hT, isDerivedComplete_of_distTriang X I hT hA hB⟩

/-- **A derived limit of a tower of derived-complete objects of `D(𝒪)` is derived complete.**
This is the ringed-site form of [Stacks, Tag 091W]: the Milnor triangle of the tower has the
countable product of its terms as its second and third objects, that product is derived complete
by `isDerivedComplete_pi`, and two-out-of-three along the triangle gives the limit. -/
theorem isDerivedComplete_of_isDerivedLimit
    (F : ℕᵒᵖ ⥤ DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (L : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (hL : IsDerivedLimit F L)
    (hF : ∀ n : ℕ, IsDerivedComplete.{u, u, u, u} X I (F.obj ⟨n⟩)) :
    IsDerivedComplete.{u, u, u, u} X I L := by
  obtain ⟨p, δ, hT⟩ := hL
  have hprod : IsDerivedComplete.{u, u, u, u} X I (∏ᶜ fun n : ℕ ↦ F.obj ⟨n⟩) :=
    isDerivedComplete_pi X I (fun n : ℕ ↦ F.obj ⟨n⟩) hF
  exact isDerivedComplete_of_distTriang X I hT hprod hprod

/-- The derived-complete objects contain a zero object. This is
`isDerivedComplete_of_isZero` in the `ObjectProperty` spelling, the idiom in which
`StacksFrontier/AlgebraicGeometry/FormalGeometry/DerivedCompletionRinged/CompleteShift.lean`
records the stability under shift and under isomorphism. -/
instance containsZero_isDerivedComplete :
    ObjectProperty.ContainsZero (IsDerivedComplete.{u, u, u, u} X I) where
  exists_zero := by
    obtain ⟨Z, hZ⟩ :=
      HasZeroObject.zero
        (C := DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    exact ⟨Z, hZ, isDerivedComplete_of_isZero X I hZ⟩

/-- The derived-complete objects satisfy two-out-of-three for the *second* object of a
distinguished triangle, which is the form `ObjectProperty.IsTriangulated` asks for: rotating the
triangle turns it into the statement for the first object, the shift of `T.obj₁` being derived
complete by `isDerivedComplete_shiftFunctor_obj`. -/
instance isTriangulatedClosed₂_isDerivedComplete :
    ObjectProperty.IsTriangulatedClosed₂ (IsDerivedComplete.{u, u, u, u} X I) where
  ext₂' T hT h₁ h₃ :=
    ObjectProperty.le_isoClosure (IsDerivedComplete.{u, u, u, u} X I) _
      (isDerivedComplete_of_distTriang X I (rot_of_distTriang T hT) h₃
        (isDerivedComplete_shiftFunctor_obj X I (1 : ℤ) h₁))

/-- **The derived-complete objects form a triangulated subcategory of `D(𝒪)`.** This is the
ringed-site form of the module-level `isDerivedComplete_isTriangulated`, and the first half of
the assertion of [Stacks, Tag 099C] that the derived-complete objects are a triangulated
subcategory closed under products; the closure under products is
`isDerivedComplete_pi`. -/
instance isTriangulated_isDerivedComplete :
    ObjectProperty.IsTriangulated (IsDerivedComplete.{u, u, u, u} X I) where
  isStableUnderShiftBy n := ⟨fun _ hK ↦ isDerivedComplete_shiftFunctor_obj X I n hK⟩

end AlgebraicGeometry.RingedSite

end
