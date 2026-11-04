module

import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.ChangeOfBaseScheme
import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactOpenGaloisDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Separated
import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.ZeroScheme

/-!
# Closed subspaces viewed over the terminal scheme

Let `Y` be an algebraic space over a scheme `S` contained in a big fppf site `B`. Viewing `Y`
over the terminal scheme `Spec ℤ` is the relocalization `Λ` along `S ⟶ Spec ℤ`
(`AlgebraicGeometry.Space.viewOverIntegers`). This file carries an antitone family of closed
subspaces of `Y` to an antitone family of closed subspaces of `Λ Y`, member by member
isomorphic to the views of the original ones, and whose intersection is isomorphic to the view
of the original intersection.

## Main results

* `AlgebraicGeometry.Space.range_viewOverIntegers_map_ι_iInf`: taking the image of the view of
  an inclusion commutes with intersections of subfunctors.
* `AlgebraicGeometry.Space.exists_closedSubspaces_viewOverIntegers`: an antitone family of
  closed subspaces of `Y` gives an antitone family of closed subspaces of the view of `Y` over
  the terminal scheme, with isomorphisms `Z' i ≅ Λ (Z i)` and `⨅ Z' ≅ Λ (⨅ Z)`.

## Implementation notes

The closed subspace attached to `Z ⊆ Y` is the image subfunctor of `Λ (Z ⟶ Y)`. As `Λ`
preserves fibre products it preserves monomorphisms, so this image is isomorphic to `Λ Z`.
A section of `Λ Y` lies in that image exactly when its underlying section of `Y` lies in `Z`
(`CategoryTheory.OverShriek.mem_range_relocalizePresheafFunctor_map_ι`), so taking images
commutes with arbitrary intersections; in particular no directedness of the index is needed.

That the view of an algebraic space is an algebraic space is
`AlgebraicGeometry.Space.isAlgebraicSpace_relocalize`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (hZ : B.Contains (⊤_ Scheme.{u}))

/-- Taking the image of the view over the terminal scheme commutes with intersections of
subfunctors. -/
theorem range_viewOverIntegers_map_ι_iInf {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {ι : Sort*}
    (Z : ι → Subfunctor F) :
    Subfunctor.range ((OverShriek.relocalizePresheafFunctor
        (⟨terminal.from S⟩ : B.obj hS ⟶ B.obj hZ)).map (⨅ i, Z i).ι) =
      ⨅ i, Subfunctor.range ((OverShriek.relocalizePresheafFunctor
        (⟨terminal.from S⟩ : B.obj hS ⟶ B.obj hZ)).map (Z i).ι) := by
  ext W x
  simp only [Subfunctor.iInf_obj, Set.mem_iInter,
    OverShriek.mem_range_relocalizePresheafFunctor_map_ι]

/-- **Closed subspaces of an inverse system, viewed over the terminal scheme.** An antitone
family `Z` of closed subspaces of an algebraic space `Y` over `S` gives an antitone family `Z'`
of closed subspaces of the view of `Y` over the terminal scheme, with `Z' i` isomorphic to the
view of `Z i` and the intersection of the `Z' i` isomorphic to the view of the intersection of
the `Z i`. -/
theorem exists_closedSubspaces_viewOverIntegers (Y : AlgebraicSpaces B S hS) {ι : Type u}
    [Preorder ι] (Z : ι → ClosedSubspaces B S hS Y.1)
    (hZmono : ∀ ⦃i j⦄, i ≤ j → (Z j).1 ≤ (Z i).1) :
    ∃ (Z' : ι → ClosedSubspaces B (⊤_ Scheme.{u}) hZ (viewOverIntegers B S hS hZ Y.1)),
      (∀ ⦃i j⦄, i ≤ j → (Z' j).1 ≤ (Z' i).1) ∧
      (∀ i, Nonempty ((Z' i).1.toFunctor ≅ viewOverIntegers B S hS hZ (Z i).1.toFunctor)) ∧
      Nonempty ((⨅ i, (Z' i).1).toFunctor ≅
        viewOverIntegers B S hS hZ (⨅ i, (Z i).1).toFunctor) := by
  let k : B.obj hS ⟶ B.obj hZ := ⟨terminal.from S⟩
  set Λ := OverShriek.relocalizePresheafFunctor k
  refine ⟨fun i => ⟨Subfunctor.range (Λ.map (Z i).1.ι),
    isClosedSubspace_range_of_isClosedImmersion B _ hZ _
      (isAlgebraicSpace_relocalize B (B.obj hS) (B.obj hZ) k _ (Z i).2.1)
      (isClosedImmersion_relocalize B S hS hZ k (Z i).2.2)⟩, ?_, ?_, ?_⟩
  · intro i j hij
    show Subfunctor.range (Λ.map (Z j).1.ι) ≤ Subfunctor.range (Λ.map (Z i).1.ι)
    rw [← Subfunctor.homOfLe_ι (hZmono hij), Λ.map_comp]
    exact Subfunctor.range_comp_le _ _
  · exact fun i => ⟨(asIso (Subfunctor.toRange (Λ.map (Z i).1.ι))).symm⟩
  · refine ⟨eqToIso ?_ ≪≫ (asIso (Subfunctor.toRange (Λ.map (⨅ i, (Z i).1).ι))).symm⟩
    exact congrArg Subfunctor.toFunctor
      (range_viewOverIntegers_map_ι_iInf B S hS hZ fun i => (Z i).1).symm

end AlgebraicGeometry.Space
