module

public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.Denominators
public import StacksFrontier.AlgebraicGeometry.ChangeOfRingsTensor.Basic
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.Invertible

/-!
# The sheaf of meromorphic sections of `L` is `L ⊗ K_X`

Let `X` be a scheme and `L` a sheaf of `𝒪_X`-modules. The sheaf `K_X(L)` of meromorphic
sections of `L` is defined as the extension of scalars of `L` along the canonical morphism
`𝒪_X ⟶ K_X` into the sheaf of total quotient rings. The Stacks project instead writes it as
the tensor product `L ⊗_{𝒪_X} K_X`. This file identifies the two, by specialising the general
comparison of extension of scalars with the sheafified tensor product to the morphism
`𝒪_X ⟶ K_X`.

The point of the identification is that the right-hand side is the image of `K_X` under the
functor `L ⊗_{𝒪_X} -`, which is an equivalence when `L` is invertible. So for invertible `L`
every statement about `K_X` transports to `K_X(L)`, which is the reduction "we may assume
`L = 𝒪_X`" that the source makes when it describes the ideal of denominators locally.

## Main definitions

* `AlgebraicGeometry.totalQuotientSheafAsModule`: `K_X`, read as a sheaf of `𝒪_X`-modules by
  restriction of scalars along `𝒪_X ⟶ K_X`.

## Main results

* `AlgebraicGeometry.meromorphicSectionSheafAsModuleIso`: `K_X(L) ≅ K_X ⊗_{𝒪_X} L`, naturally
  in `L`.
* `AlgebraicGeometry.meromorphicSectionSheafAsModuleIsoTensorLeft`: `K_X(L) ≅ L ⊗_{𝒪_X} K_X`,
  the form the source uses, obtained from the previous one by the braiding.
* `AlgebraicGeometry.isEquivalence_tensorLeftFunctor_of_isInvertible`: for invertible `L`,
  tensoring by `L` is an equivalence, so the previous isomorphism presents `K_X(L)` as the
  image of `K_X` under an equivalence.

## Implementation notes

The general comparison is
`Stacks.Sheaves.ChangeOfRings.changeOfRingsCompRestrictScalarsIso`, a natural isomorphism of
functors on sheaves of `𝒪_X`-modules; everything here is that isomorphism evaluated at `L`,
together with `Stacks.SheafOfModules.Invertible.tensorLeftFunctorSwap` for the braiding.

`AlgebraicGeometry.meromorphicSectionSheaf` fixes the two sheafification instances by a `letI`
rather than taking them from instance search. Both classes are propositions, so the instances
chosen here and the ones fixed there are the same by proof irrelevance and the comparison
applies with no transport.

## References

* [Stacks Project, Tag 01X4](https://stacks.math.columbia.edu/tag/01X4)
* [Stacks Project, Tag 02P0](https://stacks.math.columbia.edu/tag/02P0)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory TopologicalSpace

universe u

namespace AlgebraicGeometry

variable (X : Scheme.{u})

/-- The sheaf `K_X` of total quotient rings, read as a sheaf of `𝒪_X`-modules by restriction of
scalars along `𝒪_X ⟶ K_X`. This is the module that `K_X(-)` tensors by.

It is `Stacks.Sheaves.RingedToposModules.ringModSheaf` at `θ = 𝒪_X ⟶ K_X`, named here only
because that general declaration sits inside a `[SmallCategory C]` section of
`StacksFrontier/AlgebraicGeometry/Divisors/Meromorphic/DenominatorsInclusion.lean`; do not coin a
third name for it. -/
def totalQuotientSheafAsModule :
    SheafOfModules.{u} (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X)
      X.sheaf) :=
  (SheafOfModules.restrictScalars (toTotalQuotientRingSheaf X)).obj
    (SheafOfModules.unit
      (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X)
        X.totalQuotientSheaf))

/-- The sheaf of meromorphic sections of `L`, read as a sheaf of `𝒪_X`-modules, is the
sheafified tensor product `K_X ⊗_{𝒪_X} L`. -/
def meromorphicSectionSheafAsModuleIso
    (L : SheafOfModules.{u}
      (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X) X.sheaf)) :
    meromorphicSectionSheafAsModule X L ≅
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
          ⟨X.sheaf.obj, Presheaf.isSheaf_of_isSheaf_comp _ (X.sheaf.obj)
            (forget₂ CommRingCat RingCat)
            ((Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X)
              X.sheaf).property)⟩).obj ((totalQuotientSheafAsModule X)))).obj L :=
  (Stacks.Sheaves.ChangeOfRings.changeOfRingsCompRestrictScalarsIso
    (Opens.grothendieckTopology X) X.toTotalQuotientSheaf).app L

/-- The sheaf of meromorphic sections of `L` is `L ⊗_{𝒪_X} K_X`, the form in which the source
states it. -/
def meromorphicSectionSheafAsModuleIsoTensorLeft
    (L : SheafOfModules.{u}
      (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X) X.sheaf)) :
    meromorphicSectionSheafAsModule X L ≅
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
          ⟨X.sheaf.obj, Presheaf.isSheaf_of_isSheaf_comp _ (X.sheaf.obj)
            (forget₂ CommRingCat RingCat)
            ((Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X)
              X.sheaf).property)⟩).obj (L))).obj (totalQuotientSheafAsModule X) :=
  meromorphicSectionSheafAsModuleIso X L ≪≫
    Stacks.SheafOfModules.Invertible.tensorLeftFunctorSwap X.sheaf.obj
      (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X) X.sheaf).property
      L (totalQuotientSheafAsModule X)

/-- For an invertible sheaf of modules `L`, tensoring by `L` is an equivalence of the category
of sheaves of `𝒪_X`-modules. Combined with
`AlgebraicGeometry.meromorphicSectionSheafAsModuleIsoTensorLeft` this presents `K_X(L)` as the
image of `K_X` under an equivalence, which is the reduction to the case `L = 𝒪_X`. -/
theorem isEquivalence_tensorLeftFunctor_of_isInvertible
    (L : SheafOfModules.{u}
      (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X) X.sheaf))
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj
      (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X) X.sheaf).property
        L) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
        ⟨X.sheaf.obj, Presheaf.isSheaf_of_isSheaf_comp _ (X.sheaf.obj)
          (forget₂ CommRingCat RingCat)
          ((Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X)
            X.sheaf).property)⟩).obj (L))).IsEquivalence :=
  (AlgebraicGeometry.SheafOfModules.isInvertible_iff_tensorLeftFunctor_isEquivalence
    X.sheaf.obj
    (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X) X.sheaf).property
      L).mp hL

end AlgebraicGeometry
