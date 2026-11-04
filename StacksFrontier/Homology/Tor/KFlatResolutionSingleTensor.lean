module

public import StacksFrontier.Homology.KFlat.AcyclicModule
public import StacksFrontier.Homology.KFlat.BifunctorLocalization
public import StacksFrontier.Homology.KFlat.FreeResolution
public import StacksFrontier.Homology.TensorComplex.BifunctorSingleRightComplex
public import StacksFrontier.Homology.Tor.DerivedTensor

/-!
# A K-flat resolution of one factor computes the derived tensor product of two modules

Let `R` be a commutative ring, `M` and `N` two `R`-modules and `P^• ⟶ M` a K-flat resolution of
`M`. Then

`M ⊗^𝐋_R N ≅ P^• ⊗_R N`  in `D(R)`,

the right-hand side being the degreewise tensor product. Indeed a K-flat resolution `L^• ⟶ N`
computes the derived tensor product `P^• ⊗_R L^•`, and `P^•` being K-flat the induced map
`P^• ⊗_R L^• ⟶ P^• ⊗_R N[0]` is a quasi-isomorphism; the right-hand factor of the latter is
concentrated in degree zero, so its total complex is the degreewise tensor product.

## Main results

* `CochainComplex.DerivedTensor.nonempty_derivedTensor_iso_tensorRight_kFlat_resolution`: the
  derived tensor product `M ⊗^𝐋_R N` is the complex `P^• ⊗_R N`, with the second factor in the
  second tensor slot.
* `CochainComplex.DerivedTensor.nonempty_derivedTensor_iso_tensorLeft_kFlat_resolution`: the
  same with the second factor in the first tensor slot, by the symmetry of the tensor product
  of modules.

## References

* [Stacks Project, Tag 064M](https://stacks.math.columbia.edu/tag/064M)
* [Stacks Project, Tag 0BYI](https://stacks.math.columbia.edu/tag/0BYI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe u

namespace CochainComplex.DerivedTensor

attribute [local instance 10000] HasDerivedCategory.standard

variable {R : Type u} [CommRing R]

/-- **Tensoring with a K-flat complex in the first variable preserves quasi-isomorphisms.** This
is the mirror of `CochainComplex.KFlat.kFlat_tright_preserves_quasiIso`, obtained by reading
K-flatness at the transposed bifunctor. -/
theorem quasiIso_tleftCochain_map_of_kFlat (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : CochainComplex.KFlat.{u, u} P) {X Y : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : X ⟶ Y) (hf : QuasiIso f) :
    QuasiIso ((TleftCochain P).map f) :=
  CochainComplex.KFlatBifunctor.quasiIso_of_kFlatLeft (curriedTensor (ModuleCat.{u} R)) P
    (CochainComplex.KFlat.kFlatLeft_of_kFlat.{u, u} hP) f hf

/-- **A K-flat resolution of `M` computes `M ⊗^𝐋_R N` as `P^• ⊗_R N`.** A K-flat resolution
`L^• ⟶ N` turns the derived tensor product into the total complex `P^• ⊗_R L^•`; tensoring with
the K-flat `P^•` carries `L^• ⟶ N[0]` to a quasi-isomorphism; and the total complex of
`P^• ⊗_R N[0]` is the degreewise tensor product. -/
theorem nonempty_derivedTensor_iso_tensorRight_kFlat_resolution (M N : ModuleCat.{u} R)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (hP : CochainComplex.KFlat.{u, u} P)
    (g : P ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M) (hg : QuasiIso g) :
    Nonempty (((canonicalDerivedTensorProduct R).tensor.obj
        (DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M))).obj
        (DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj N)) ≅
      DerivedCategory.Q.obj
        ((((curriedTensor (ModuleCat.{u} R)).flip.obj N).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P)) := by
  obtain ⟨L₀, f₀, hL₀, -, -, hf₀⟩ := CochainComplex.KFlat.exists_free_kFlat_resolution N
  have h₃ : IsIso (DerivedCategory.Q.map ((TleftCochain P).map f₀)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr
      (quasiIso_tleftCochain_map_of_kFlat P hP f₀ hf₀)
  exact ⟨Iso.app ((canonicalDerivedTensorProduct R).tensor.mapIso
        (asIso (DerivedCategory.Q.map g)).symm) _ ≪≫
      ((canonicalDerivedTensorProduct R).tensor.obj (DerivedCategory.Q.obj P)).mapIso
        (asIso (DerivedCategory.Q.map f₀)).symm ≪≫
      (canonicalDerivedTensorProduct R).comparison P L₀ hP hL₀ ≪≫
      @asIso _ _ _ _ (DerivedCategory.Q.map ((TleftCochain P).map f₀)) h₃ ≪≫
      DerivedCategory.Q.mapIso (HomologicalComplex.mapBifunctorSingleRightIso
        (curriedTensor (ModuleCat.{u} R)) P N)⟩

/-- **A K-flat resolution of `M` computes `M ⊗^𝐋_R N` as `N ⊗_R P^•`.** This is
`nonempty_derivedTensor_iso_tensorRight_kFlat_resolution` moved across the symmetry of the tensor
product of modules. -/
theorem nonempty_derivedTensor_iso_tensorLeft_kFlat_resolution (M N : ModuleCat.{u} R)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (hP : CochainComplex.KFlat.{u, u} P)
    (g : P ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M) (hg : QuasiIso g) :
    Nonempty (((canonicalDerivedTensorProduct R).tensor.obj
        (DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M))).obj
        (DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj N)) ≅
      DerivedCategory.Q.obj
        ((((curriedTensor (ModuleCat.{u} R)).obj N).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P)) :=
  (nonempty_derivedTensor_iso_tensorRight_kFlat_resolution M N P hP g hg).map fun e =>
    e ≪≫ DerivedCategory.Q.mapIso
      ((NatIso.mapHomologicalComplex
        ((BraidedCategory.curriedBraidingNatIso (ModuleCat.{u} R)).app N).symm
        (ComplexShape.up ℤ)).app P)

end CochainComplex.DerivedTensor

end
