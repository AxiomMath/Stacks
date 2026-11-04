module

public import StacksFrontier.Homology.TorAmplitude.Comparison
public import StacksFrontier.Homology.Tor.DerivedTensor

/-!
# The derived tensor product against a K-flat complex is the ordinary one

Let `A` be a commutative ring and let `L` be a K-flat cochain complex of `A`-modules. Tensoring
with `L` sends quasi-isomorphisms to quasi-isomorphisms, so the ordinary total tensor product
`C ⊗ L` computes the derived tensor product of the classes of `C` and `L` for an *arbitrary*
cochain complex `C`, not only for a K-flat one. In particular the derived tensor product vanishes
as soon as `C ⊗ L` is acyclic.

This is the bridge between an explicit model of an object of the derived category and the
vanishing of its derived tensor product: the vanishing may be checked on any complex
representing the object, which is what a Čech, Koszul or injective-resolution model provides.

## Main results

* `Stacks.DerivedTensor.isZero_Q_obj_of_acyclic`: an acyclic complex is a zero object of the
  derived category.
* `Stacks.DerivedTensor.nonempty_derivedTensor_iso_tensor_of_kFlat_right`: the derived tensor
  product of the classes of `C` and `L` is the class of `C ⊗ L`, for `L` K-flat and `C`
  arbitrary.
* `Stacks.DerivedTensor.isZero_derivedTensor_of_acyclic_tensor_kFlat`: hence the derived tensor
  product vanishes when `C ⊗ L` is acyclic.
* `Stacks.DerivedTensor.isZero_derivedTensor_of_acyclic_tensor_kFlat_of_iso`: the same for two
  objects of the derived category presented by such complexes.

## Implementation notes

The characterization of the canonical derived tensor product of [Stacks, Tag 0BYI] applies only
when both factors are K-flat, so the proof interposes a K-flat resolution `C' ⟶ C` ([Stacks, Tag
06Y4]) and moves back along it: in the derived category the resolution becomes an isomorphism,
and `C' ⊗ L ⟶ C ⊗ L` is a quasi-isomorphism because `L` is K-flat ([Stacks, Tag 06Y0], in the
form `StacksDraft.TorAmplitude.quasiIso_tensorRight_map`).

## References

* [Stacks Project, Tag 0BYI](https://stacks.math.columbia.edu/tag/0BYI)
* [Stacks Project, Tag 06Y0](https://stacks.math.columbia.edu/tag/06Y0)
* [Stacks Project, Tag 06Y4](https://stacks.math.columbia.edu/tag/06Y4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ZeroObject
open CategoryTheory.MonoidalCategory
open CochainComplex.DerivedTensor StacksDraft.TorAmplitude

universe u

namespace Stacks.DerivedTensor

attribute [local instance] HasDerivedCategory.standard

variable (A : Type u) [CommRing A]

/-- **An acyclic complex is a zero object of the derived category.** The zero morphism to the
zero complex is a quasi-isomorphism, so it becomes an isomorphism in the derived category. -/
theorem isZero_Q_obj_of_acyclic (K : CochainComplex (ModuleCat.{u} A) ℤ) (hK : K.Acyclic) :
    IsZero (DerivedCategory.Q.obj K) := by
  have hzero : ∀ i : ℤ, IsZero ((0 : CochainComplex (ModuleCat.{u} A) ℤ).homology i) := fun i =>
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (ComplexShape.up ℤ) i).map_isZero
      (isZero_zero _)
  have hq : QuasiIso (0 : K ⟶ (0 : CochainComplex (ModuleCat.{u} A) ℤ)) := by
    rw [quasiIso_iff]
    intro i
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact (hK i).isZero_homology.isIso (hzero i) _
  have := hq
  have hiso : IsIso (DerivedCategory.Q.map (0 : K ⟶ (0 : CochainComplex (ModuleCat.{u} A) ℤ))) :=
    inferInstance
  have hQzero : IsZero (DerivedCategory.Q.obj (0 : CochainComplex (ModuleCat.{u} A) ℤ)) :=
    DerivedCategory.Q.map_isZero (isZero_zero _)
  exact hQzero.of_iso (asIso (DerivedCategory.Q.map
    (0 : K ⟶ (0 : CochainComplex (ModuleCat.{u} A) ℤ))))

/-- **The ordinary total tensor product with a K-flat complex computes the derived tensor
product.** The other factor is an arbitrary cochain complex. -/
theorem nonempty_derivedTensor_iso_tensor_of_kFlat_right
    (C L : CochainComplex (ModuleCat.{u} A) ℤ) (hL : L.KFlat) :
    Nonempty (((canonicalDerivedTensorProductFunctor A).obj (DerivedCategory.Q.obj C)).obj
      (DerivedCategory.Q.obj L) ≅ DerivedCategory.Q.obj (tensorObj C L)) := by
  obtain ⟨C', π, hC', -, hπ, -⟩ := CochainComplex.KFlat.exists_kFlat_resolution C
  have := hπ
  have hqi : QuasiIso ((tensorRight L).map π) := quasiIso_tensorRight_map hL π
  have := hqi
  let T := canonicalDerivedTensorProduct A
  let eC : DerivedCategory.Q.obj C' ≅ DerivedCategory.Q.obj C := asIso (DerivedCategory.Q.map π)
  let eT : DerivedCategory.Q.obj (tensorObj C' L) ≅ DerivedCategory.Q.obj (tensorObj C L) :=
    asIso (DerivedCategory.Q.map ((tensorRight L).map π))
  exact ⟨((T.tensor.mapIso eC).app (DerivedCategory.Q.obj L)).symm ≪≫
    T.comparison C' L hC' hL ≪≫ eT⟩

/-- **The derived tensor product vanishes as soon as the ordinary one does.** For `L` K-flat and
`C` an arbitrary cochain complex, acyclicity of `C ⊗ L` makes the derived tensor product of the
classes of `C` and `L` a zero object. -/
theorem isZero_derivedTensor_of_acyclic_tensor_kFlat
    (C L : CochainComplex (ModuleCat.{u} A) ℤ) (hL : L.KFlat) (hacyclic : (tensorObj C L).Acyclic) :
    IsZero (((canonicalDerivedTensorProductFunctor A).obj (DerivedCategory.Q.obj C)).obj
      (DerivedCategory.Q.obj L)) := by
  obtain ⟨e⟩ := nonempty_derivedTensor_iso_tensor_of_kFlat_right A C L hL
  exact (isZero_Q_obj_of_acyclic A (tensorObj C L) hacyclic).of_iso e

/-- **The derived tensor product of two objects of the derived category vanishes as soon as some
pair of complexes representing them has acyclic tensor product.** Only the right-hand complex
need be K-flat; the left-hand one is arbitrary. This is the form in which an explicit model of an
object — an injective resolution, a Koszul complex — is fed to the vanishing. -/
theorem isZero_derivedTensor_of_acyclic_tensor_kFlat_of_iso
    {X Y : DerivedCategory (ModuleCat.{u} A)} (C L : CochainComplex (ModuleCat.{u} A) ℤ)
    (hL : L.KFlat) (eC : DerivedCategory.Q.obj C ≅ X) (eL : DerivedCategory.Q.obj L ≅ Y)
    (hacyclic : (tensorObj C L).Acyclic) :
    IsZero (((canonicalDerivedTensorProductFunctor A).obj X).obj Y) :=
  (isZero_derivedTensor_of_acyclic_tensor_kFlat A C L hL hacyclic).of_iso
    ((((canonicalDerivedTensorProductFunctor A).mapIso eC).app Y).symm ≪≫
      (((canonicalDerivedTensorProductFunctor A).obj (DerivedCategory.Q.obj C)).mapIso eL).symm)

end Stacks.DerivedTensor

end
