module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.RingTheory.Flat.Localization
public import StacksFrontier.AlgebraicGeometry.Pullback.StalkFromSpecStalk

/-!
# Local rings along the spectrum of a field extension

For a field extension `K/k`, the morphism `Spec K ⟶ Spec k` acts on local rings compatibly
with the two structure maps out of `k`.

## Main results

* `AlgebraicGeometry.stalkMap_spec_comp_algebraMap`: the stalk map of `Spec K ⟶ Spec k` at a
  point `y`, transported along the equality identifying the image of `y`, intertwines the
  canonical maps `k → O_{Spec k, z}` and `k → K → O_{Spec K, y}`.

## Implementation notes

The equality between the chosen point of `Spec k` and the image of `y` is carried by an
`eqToHom` on stalks, so that the two sides are maps out of the same local ring.

The presentation of the local ring of a fibre product as a localization of a tensor product
is `AlgebraicGeometry.BaseChangeStalk.pullback_stalk_isLocalization`.
-/

@[expose] public section

open CategoryTheory Limits

namespace AlgebraicGeometry

universe u

/-- On the spectrum of a field extension, the stalk map of the induced morphism of spectra
intertwines the two canonical maps from the ground field into the local rings. -/
public lemma stalkMap_spec_comp_algebraMap
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    (y : Spec (.of K)) (z : Spec (.of k))
    (h : z = Spec.map (CommRingCat.ofHom (algebraMap k K)) y) :
    let : Algebra k ((Spec (.of k)).presheaf.stalk z) := StructureSheaf.stalkAlgebra k z
    let : Algebra K ((Spec (.of K)).presheaf.stalk y) := StructureSheaf.stalkAlgebra K y
    (((eqToHom (congrArg (Spec (.of k)).presheaf.stalk h)) ≫
      (Spec.map (CommRingCat.ofHom (algebraMap k K))).stalkMap y).hom).comp
        (algebraMap k ((Spec (.of k)).presheaf.stalk z)) =
      (algebraMap K ((Spec (.of K)).presheaf.stalk y)).comp (algebraMap k K) := by
  subst z
  ext a
  exact stalkMap_toStalk_apply (CommRingCat.ofHom (algebraMap k K)) y a

end AlgebraicGeometry
