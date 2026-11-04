module

public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.YonedaKernelAcyclic
public import StacksFrontier.CategoryTheory.Triangulated.NeemanThomason
public import StacksFrontier.CategoryTheory.Triangulated.ThickImage

/-!
# `Z = Ac` without resolutions, by Neeman–Thomason

Let `C : DGCategory.{v, v} R` be a differential graded category over a commutative ring `R` whose
objects and whose morphism modules lie in the same universe `v`, let
`Φ = K(h) : K(C) ⥤ K(Mod^dg(C))` be the differential graded Yoneda functor on homotopy
categories, let `G : ι → C.Obj` be a family of objects of `C` indexed by a type `ι : Type v`, and
let `N = ⟨h_{G i}⟩`, `Z = Φ⁻¹ N` as in
`StacksFrontier/CategoryTheory/DifferentialGraded/RightModule/YonedaKernelAcyclic.lean`.

That file proves the inclusion `Z ≤ Ac` from the existence of `Ac`-resolutions — in the intended
reading `K`-injective resolutions, [Stacks, Tag 079P] — which is strictly stronger than the
situation of [Stacks, Tag 09LJ], where `A` is an arbitrary abelian category. This file proves the
same inclusion with no resolution hypothesis whatever, by the route the source's own proof takes:
the Neeman–Thomason description of the compact objects of a compactly generated localizing
subcategory.

## The argument

`h_X = Φ X` is a compact object of `K(Mod^dg(C))`
(`DGCategory.RightModule.isCompactObject_yonedaObjK`), so if it lies in `N` then by
`CategoryTheory.ObjectProperty.localizingClosure_inf_isCompactObject_eq_triangEnvelope` it lies in
the *thick* closure `⟨h_{G i}⟩` of the generators — not merely in the localizing one. Thickness is
what can be transported back along `Φ`: by
`CategoryTheory.ObjectProperty.isTriangulated_retractClosure_map` the retract closure of the image
`Φ(Ac)` of a thick subcategory `Ac` of `K(C)` is a thick subcategory of `K(Mod^dg(C))`, it
contains every generator `h_{G i} = Φ (G i)` because `G i` is in `Ac`, and therefore it contains
`⟨h_{G i}⟩`. So `Φ X` is a retract of some `Φ Y` with `Y` in `Ac`, and full faithfulness of `Φ`
(`DGCategory.full_yonedaOnK`, `DGCategory.faithful_yonedaOnK`) turns that into a retract of `Y` in
`K(C)`, whence `X` is in `Ac`.

Nothing here is an acyclicity statement about the module `h_X`, and nothing could be: `h_X` is an
acyclic differential graded module exactly when `X` is a zero object of `K(C)`
(`DGCategory.RightModule.forall_hom_eq_zero_iff_isAcyclic`).

## What replaces the resolution hypothesis, and what it costs

The resolution hypothesis `hres` of `DGCategory.RightModule.yonedaInverseImage_le` is replaced by
two conditions, and neither is a resolution statement in disguise.

* `Ac` is a *triangulated* subcategory, not merely one closed under isomorphisms, shifts and
  retracts. Together with the retract closure already assumed there this says that `Ac` is thick,
  which the acyclic complexes of any abelian category are, unconditionally: acyclicity is closed
  under isomorphism, shift, cones and direct summands.
* A universe condition: `C` is a `DGCategory.{v, v}` and the index type `ι` is a nonempty
  `Type v`, where `DGCategory.RightModule.yonedaInverseImage_eq` allows `C : DGCategory.{v, u}`
  and an arbitrary `ι`. This is a genuine restriction and it is not removable by any rephrasing
  here. The reason is the cell-tower construction behind [Stacks, Tag 09SN], which indexes a
  direct sum by the triples `(i, m, φ)` with `φ : (h_{G i})⟦m⟧ ⟶ M`: that index type lies in the
  *morphism* universe of `K(Mod^dg(C))`, which is `max u v`, while the direct sums of
  `K(Mod^dg(C))` are indexed by `Type v`
  (`DGCategory.RightModule.hasCoproducts_rightModuleHomotopyCategory`). So the tower exists only
  when `max u v = v`, that is when `u ≤ v`. It costs the chain nothing, because
  `StacksFrontier/CategoryTheory/DifferentialGraded/RightModule/DerivedHomChainIdentification.lean`
  states `DGCategory.RightModule.exists_chainEquivReflectorEvaluation_of_yonedaInverseImage_eq`,
  the consumer of this equality, for `C : DGCategory.{v, v} R` and `G : ι → C.Obj` with
  `ι : Type v` already — it is the condition step 1 of [Stacks, Tag 09LK] carries through Brown
  representability. With `C.Obj` in `Type v` the tautological enumeration of `Ac` by `Subtype Ac`
  has index type in `Type v`, and nonemptiness is free because a thick `Ac` contains a zero
  object.

## Main results

* `DGCategory.RightModule.yonedaInverseImage_le_of_isTriangulated`: the inclusion `Z ≤ Ac` for a
  thick `Ac`, with no resolution hypothesis.
* `DGCategory.RightModule.yonedaInverseImage_eq_of_isTriangulated`: the equality `Z = Ac`.

## References

* [Stacks Project, Tag 09LK](https://stacks.math.columbia.edu/tag/09LK)
* [Stacks Project, Tag 09SR](https://stacks.math.columbia.edu/tag/09SR)
-/

@[expose] public section

namespace DGCategory

universe v r

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.ObjectProperty

variable {R : Type r} [CommRing R] (C : DGCategory.{v, v} R)

namespace RightModule

attribute [local implicit_reducible] DGCategory.K

variable {ι : Type v} (G : ι → C.Obj)

section

variable [Preadditive C.K] [HasZeroObject C.K] [HasShift C.K ℤ]
  [∀ n : ℤ, (shiftFunctor C.K n).Additive] [Pretriangulated C.K]
  [((yonedaDGFunctor C).onK).CommShift ℤ] [((yonedaDGFunctor C).onK).IsTriangulated]

/-- **The inclusion `Z ≤ Ac`, with no resolutions.** Let `Ac` be a thick subcategory of `K(C)` —
closed under isomorphisms, a triangulated subcategory, and closed under retracts — containing
every `G i`, with `ι` a nonempty `Type v`. Then `Z = Φ⁻¹ N` is contained in `Ac`.

The representable `h_X = Φ X` is compact, so membership in the localizing subcategory `N`
upgrades to membership in the thick closure `⟨h_{G i}⟩` by the Neeman–Thomason theorem
(`CategoryTheory.ObjectProperty.localizingClosure_inf_isCompactObject_eq_triangEnvelope`). The
retract closure of `Φ(Ac)` is a thick subcategory containing the generators
(`CategoryTheory.ObjectProperty.isTriangulated_retractClosure_map`), hence contains that closure,
so `Φ X` is a retract of `Φ Y` for some `Y` in `Ac`; full faithfulness of `Φ` turns this into a
retract of `Y` in `K(C)`, and `Ac` is closed under retracts. -/
theorem yonedaInverseImage_le_of_isTriangulated [Nonempty ι] (Ac : ObjectProperty C.K)
    [Ac.IsClosedUnderIsomorphisms] [Ac.IsTriangulated] [Ac.IsStableUnderRetracts]
    (hGAc : ∀ i, Ac (G i : C.K)) :
    yonedaInverseImage C G ≤ Ac := by
  have : ∀ i, IsCompactObject.{v}
      (yonedaObjK (G i) : (rightModuleCategory.{v} C).K) :=
    fun i ↦ isCompactObject_yonedaObjK (G i)
  have := isTriangulated_retractClosure_map Ac ((yonedaDGFunctor C).onK)
  intro X hX
  -- `h_X` lies in `N` and is compact, hence lies in the thick closure of the generators.
  have hmem : ((ofObj fun i ↦ yonedaObjK (G i)).localizingClosure.{v} ⊓
      IsCompactObject.{v, _, _} (C := (rightModuleCategory.{v} C).K))
        (((yonedaDGFunctor C).onK).obj X) :=
    ⟨hX, isCompactObject_of_yonedaImage C ⟨X, ⟨Iso.refl _⟩⟩⟩
  rw [localizingClosure_inf_isCompactObject_eq_triangEnvelope] at hmem
  -- The thick closure of `Φ(Ac)` contains the generators, hence their thick closure.
  have hle : (ofObj fun i ↦ yonedaObjK (G i)) ≤
      (Ac.map ((yonedaDGFunctor C).onK)).retractClosure :=
    (ofObj_le_iff _ _).2 fun i ↦ (Ac.map ((yonedaDGFunctor C).onK)).le_retractClosure _
      (Ac.prop_map_obj ((yonedaDGFunctor C).onK) (hGAc i))
  exact prop_of_retractClosure_map_obj Ac ((yonedaDGFunctor C).onK)
    ((triangEnvelope_le_iff _).2 hle _ hmem)

/-- **`Z = Ac`, with no resolutions.** The subcategory `Z = Φ⁻¹ N` at which
`DGCategory.RightModule.isLocalization_yonedaLift_comp` localizes is exactly `Ac`, as soon as `Ac`
is a thick subcategory of `K(C)` and `G` enumerates it up to isomorphism, the index type being a
nonempty `Type v`. In the intended reading — `C` the differential graded
category of complexes of an abelian category, `Ac` the acyclic complexes and `G` an enumeration of
them — this identifies the target of that localization with the derived category of the abelian
category, with no hypothesis on the abelian category beyond what [Stacks, Tag 09LJ] assumes.

This is `DGCategory.RightModule.yonedaInverseImage_eq` with the resolution hypothesis traded for
thickness of `Ac` and for the universe condition `C : DGCategory.{v, v}`, `ι : Type v`. -/
theorem yonedaInverseImage_eq_of_isTriangulated [Nonempty ι] (Ac : ObjectProperty C.K)
    [Ac.IsClosedUnderIsomorphisms] [Ac.IsTriangulated] [Ac.IsStableUnderRetracts]
    (hG : ∀ X : C.K, Ac X → ∃ i, Nonempty (X ≅ (G i : C.K)))
    (hGAc : ∀ i, Ac (G i : C.K)) :
    yonedaInverseImage C G = Ac :=
  le_antisymm (yonedaInverseImage_le_of_isTriangulated C G Ac hGAc)
    (le_yonedaInverseImage C G Ac hG)

end

end RightModule

end DGCategory

end
