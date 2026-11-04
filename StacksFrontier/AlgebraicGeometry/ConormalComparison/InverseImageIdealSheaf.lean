module

public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.ImmersionStalk
public import StacksFrontier.AlgebraicGeometry.SheafifyStalk.StalkMap
public import StacksFrontier.Topology.Sheaves.Modules.ConormalSheafStalk

/-!
# The inverse image of the defining ideal sheaf is the kernel of the structural homomorphism

Let `i : Z ⟶ X` be a morphism of schemes whose base map is an embedding and let `ℐ ⊆ 𝒪_X` be
its defining ideal sheaf, the ideal subsheaf of sections dying in `i_*𝒪_Z`.  The structural
homomorphism `i^{-1}𝒪_X ⟶ 𝒪_Z` has a kernel ideal, and this file identifies it with `i^{-1}ℐ`:
on each stalk the kernel of the structural homomorphism is, under the canonical identification
`(i^{-1}𝒪_X)_z ≅ 𝒪_{X, i z}`, the ideal of germs of sections of `ℐ`.

## Main results

* `Stacks.Conormal.InverseImage.stalkKernelIdeal_eq_comap_ker_stalkMap`: the kernel of the
  structural homomorphism on the stalk at `z` is the inverse image, along
  `(i^{-1}𝒪_X)_z ≅ 𝒪_{X, i z}`, of the kernel of the map of local rings `𝒪_{X, i z} ⟶ 𝒪_{Z,z}`.
* `Stacks.Conormal.InverseImage.stalkKernelIdeal_eq_comap_stalkIdeal`: the same ideal is the
  inverse image of the stalk of the defining ideal sheaf.  This is the stalkwise form of
  `i^{-1}ℐ = ker(i^{-1}𝒪_X ⟶ 𝒪_Z)`.
* `Stacks.Conormal.InverseImage.mem_stalkKernelIdeal_iff_exists_mem_definingIdealOfHom`: its
  germ form, with the section of `ℐ` exhibited.
* `Stacks.Conormal.InverseImage.ker_stalkMap_comp` and
  `Stacks.Conormal.InverseImage.stalkKernelIdeal_comp_eq_comap_ker_stalkMap`: the same ideal
  read on a factorization `i = k ≫ j`.

## References

* [Stacks Project, Section 29.2 (Tag 01R2)](https://stacks.math.columbia.edu/tag/01R2)
* [Stacks Project, Lemma 29.2.1 (Tag 01R3)](https://stacks.math.columbia.edu/tag/01R3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.RegularIdealSheaf
open Stacks.SheafifyStalk

universe u

namespace Stacks.Conormal.InverseImage

variable {Z X : Scheme.{u}} (i : Z ⟶ X) (z : Z)

/-- **The stalk of the structural homomorphism is `i`'s stalk map, read through the comparison
isomorphism.**  Applied to an element of `(i^{-1}𝒪_X)_z`, the stalk of `i^{-1}𝒪_X ⟶ 𝒪_Z` is the
map of local rings `𝒪_{X, i z} ⟶ 𝒪_{Z, z}` evaluated at the transported element. -/
theorem stalkFunctor_map_inverseImageStructureMap_hom :
    ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} z).map
        (AlgebraicGeometry.inverseImageStructureMap i).hom).hom =
      (i.stalkMap z).hom.comp (stalkInverseImageStructureSheafIso i z).hom.hom := by
  rw [← CommRingCat.hom_comp]
  exact congrArg CommRingCat.Hom.hom
    (stalkInverseImageStructureSheafIso_hom_comp_stalkMap i z).symm

/-- **The kernel of the structural homomorphism on stalks is the kernel of the map of local
rings.**  The ideal of `(i^{-1}𝒪_X)_z` cut out by `i^{-1}𝒪_X ⟶ 𝒪_Z` is the inverse image, along
the comparison isomorphism `(i^{-1}𝒪_X)_z ≅ 𝒪_{X, i z}`, of `ker(𝒪_{X, i z} ⟶ 𝒪_{Z, z})`. -/
theorem stalkKernelIdeal_eq_comap_ker_stalkMap :
    Stacks.Sites.Conormal.stalkKernelIdeal
        (AlgebraicGeometry.inverseImageStructureMap i).hom z =
      (RingHom.ker (i.stalkMap z).hom).comap
        (stalkInverseImageStructureSheafIso i z).hom.hom :=
  (congrArg RingHom.ker (stalkFunctor_map_inverseImageStructureMap_hom i z)).trans
    (RingHom.comap_ker _ _).symm

variable [IsImmersion i]

/-- **The inverse image of the defining ideal sheaf is the kernel of the structural
homomorphism.**  For a morphism of schemes whose base map is an embedding, the ideal of
`(i^{-1}𝒪_X)_z` cut out by `i^{-1}𝒪_X ⟶ 𝒪_Z` is the inverse image, along the comparison
isomorphism `(i^{-1}𝒪_X)_z ≅ 𝒪_{X, i z}`, of the stalk at `i z` of the defining ideal sheaf
of `i`. -/
theorem stalkKernelIdeal_eq_comap_stalkIdeal :
    Stacks.Sites.Conormal.stalkKernelIdeal
        (AlgebraicGeometry.inverseImageStructureMap i).hom z =
      (Stacks.RingedSpace.stalkIdeal (X := X.toLocallyRingedSpace)
        (definingIdealOfHom i) (i.base z)).comap
          (stalkInverseImageStructureSheafIso i z).hom.hom := by
  rw [stalkKernelIdeal_eq_comap_ker_stalkMap i z,
    ← stalkIdeal_definingIdealOfHom_eq_ker i z]

/-- **The germ form of the identification.**  An element of `(i^{-1}𝒪_X)_z` is killed by the
structural homomorphism exactly when its image in `𝒪_{X, i z}` is the germ of a section of the
defining ideal sheaf of `i`. -/
theorem mem_stalkKernelIdeal_iff_exists_mem_definingIdealOfHom
    (y : ToType (((TopCat.Sheaf.pullback CommRingCat.{u} i.base).obj X.sheaf).presheaf.stalk z)) :
    y ∈ Stacks.Sites.Conormal.stalkKernelIdeal
        (AlgebraicGeometry.inverseImageStructureMap i).hom z ↔
      ∃ (V : X.Opens) (hV : i.base z ∈ V) (s : X.presheaf.obj (op V)),
        s ∈ (definingIdealOfHom i).obj (op V) ∧
          X.presheaf.germ V (i.base z) hV s =
            (stalkInverseImageStructureSheafIso i z).hom.hom y := by
  rw [stalkKernelIdeal_eq_comap_stalkIdeal i z, Ideal.mem_comap]
  exact Stacks.RingedSpace.mem_stalkIdeal_iff (definingIdealOfHom i)

section Factorization

variable {U : Scheme.{u}} (k : Z ⟶ U) (j : U ⟶ X)

/-- **The kernel of the map of local rings of a composite.**  For `k : Z ⟶ U` followed by
`j : U ⟶ X`, the kernel of `𝒪_{X, (k ≫ j) z} ⟶ 𝒪_{Z, z}` is the inverse image of
`ker(𝒪_{U, k z} ⟶ 𝒪_{Z, z})` along the stalk map of `j`. -/
theorem ker_stalkMap_comp :
    RingHom.ker ((k ≫ j).stalkMap z).hom =
      (RingHom.ker (k.stalkMap z).hom).comap (j.stalkMap (k.base z)).hom :=
  ((congrArg RingHom.ker (congrArg CommRingCat.Hom.hom
          (Scheme.Hom.stalkMap_comp k j z))).trans
        (congrArg RingHom.ker
          (CommRingCat.hom_comp (j.stalkMap (k.base z)) (k.stalkMap z)))).trans
    (RingHom.comap_ker _ _).symm

/-- **The identification read on a factorization.**  The ideal of `(i^{-1}𝒪_X)_z` cut out by the
structural homomorphism `i^{-1}𝒪_X ⟶ 𝒪_Z`, for `i = k ≫ j`, is the inverse image of
`ker(𝒪_{U, k z} ⟶ 𝒪_{Z, z})` along the comparison isomorphism `(i^{-1}𝒪_X)_z ≅ 𝒪_{X, i z}`
followed by the stalk map of `j`. -/
theorem stalkKernelIdeal_comp_eq_comap_ker_stalkMap :
    Stacks.Sites.Conormal.stalkKernelIdeal
        (AlgebraicGeometry.inverseImageStructureMap (k ≫ j)).hom z =
      (RingHom.ker (k.stalkMap z).hom).comap
        ((j.stalkMap (k.base z)).hom.comp
          (stalkInverseImageStructureSheafIso (k ≫ j) z).hom.hom) := by
  rw [stalkKernelIdeal_eq_comap_ker_stalkMap (k ≫ j) z,
    ker_stalkMap_comp (k := k) (j := j) (z := z)]
  exact Ideal.comap_comap _ _

end Factorization

end Stacks.Conormal.InverseImage

end
