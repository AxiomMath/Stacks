module

public import StacksFrontier.Cotangent.AtiyahClassBigSiteDisplayed
public import StacksFrontier.Homology.Tor.DerivedTensorToTotalComplex
import StacksCore.Tactic.StacksAttribute

/-!
# The Atiyah class of a module as a morphism of `D(B)`

[Stacks, Tag 09DE] calls the last arrow `M ⟶ (L_{B/A} ⊗^𝐋_B M)[1]` of the distinguished triangle
(92.17.0.1) of [Stacks, Tag 09DD] the *Atiyah class* of the `B`-module `M`. The triangle is
obtained by applying `Lπ_!` of [Stacks, Tag 09CZ] to the sequence of first principal parts on the
site `C_{B/A}`, and its endpoints are identified with `L_{B/A} ⊗^𝐋_B M` and `M` by [Stacks,
Tag 08PT] together with the flatness of the terms of `L_{B/A}`, and by [Stacks, Tag 08QE].

This file names that arrow outright, as a morphism of the derived category of `B`-modules. Both
identifications are canonical isomorphisms here:

* the third term is `CommAlgCat.polynomialAtiyahTriangleObj₃Iso`, [Tag 08QE] at the site;
* the first term is `CommAlgCat.atiyahFirstVertexDisplayedIso`, the chain of [Tag 08PT],
  [Tag 08PU] and [Tag 09CZ] at the site (`CommAlgCat.atiyahFirstVertexMooreIso`,
  `CommAlgCat.atiyahFirstVertexDiagramIso`, `CommAlgCat.atiyahMooreTensorIso`), closed by the
  *canonical* map `QK ⊗^𝐋 QL ⟶ Q(K ⊗ L)` of
  `CochainComplex.DerivedTensor.ToTotal.canonicalDerivedToTensorNatTrans`, which is invertible
  because the universe lift of `L_{B/A}` is K-flat (`CommAlgCat.kFlat_moduleLiftCotangentComplex`).
  This is the source's "`L_{B/A} ⊗_B M = L_{B/A} ⊗_B^𝐋 M` by the flatness of the terms of
  `L_{B/A}`", and no K-flat resolution is chosen in it.

## Main definitions

* `CommAlgCat.atiyahFirstVertexDisplayedIso`: `Lπ_!(Ω_{𝒪/A} ⊗_𝒪 M̲) ≅ L_{B/A} ⊗^𝐋_B M` in `D(B)`.
* `CommAlgCat.atiyahClass`: **the Atiyah class** `M ⟶ (L_{B/A} ⊗^𝐋_B M)[1]` in `D(B)`.

## Main results

* `CommAlgCat.atiyahDisplayedTriangle_distinguished`: the displayed triangle
  `L_{B/A} ⊗^𝐋_B M ⟶ Lπ_!(P¹_{𝒪/A}(M)) ⟶ M ⟶ (L_{B/A} ⊗^𝐋_B M)[1]` of (92.17.0.1), whose last
  arrow is `CommAlgCat.atiyahClass`, is distinguished.

## Implementation notes

The site `C_{B/A}` is read on its `CategoryTheory.AsSmall` model `CommAlgCat.atiyahSite`, whose
ringed point has the ring `ULift B`; so `D(B)` is the derived category of
`ModuleCat.{u + 1} (ULift B)` and `M` is a module over it, as in
`StacksFrontier/Cotangent/AtiyahClass.lean`.

## References

* [Stacks Project, Tag 09DE](https://stacks.math.columbia.edu/tag/09DE)
* [Stacks Project, Tag 09DD](https://stacks.math.columbia.edu/tag/09DD)
* [Stacks Project, Tag 08PT](https://stacks.math.columbia.edu/tag/08PT)
* [Stacks Project, Tag 08QE](https://stacks.math.columbia.edu/tag/08QE)
* [Stacks Project, Tag 09CZ](https://stacks.math.columbia.edu/tag/09CZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Pretriangulated
open CochainComplex.DerivedTensor
open Stacks.ChaoticSite.ModuleValued

universe u

namespace CommAlgCat

attribute [local instance 2000] HasDerivedCategory.standard

variable (A : Type u) [CommRing A] (B : CommAlgCat.{u} A)
  (M : ModuleCat.{u + 1} (ULift.{u + 1} (B : Type u)))

/-- **`L_{B/A} ⊗^𝐋_B M = L_{B/A} ⊗_B M`, canonically**: the canonical map from the derived tensor
product to the ordinary total tensor complex, at `M[0]` and the universe lift of `L_{B/A}`, which
is invertible because the latter is K-flat. -/
def atiyahDisplayedObj₁TensorIso :
    atiyahDisplayedObj₁ A B M ≅
      DerivedCategory.Q.obj (atiyahModuleSingleComplex A B M ⊗ moduleLiftCotangentComplex A B) :=
  derivedTensorProductCommIso _ _ ≪≫
    @asIso _ _ _ _
      ((ToTotal.canonicalDerivedToTensorNatTrans (ULift.{u + 1} (B : Type u))).app
        (atiyahModuleSingleComplex A B M, moduleLiftCotangentComplex A B))
      (ToTotal.isIso_derivedToTensorNatTrans_app _ _ _ (kFlat_moduleLiftCotangentComplex A B))

/-- **The first term of the Atiyah triangle at the site `C_{B/A}` is `L_{B/A} ⊗^𝐋_B M`**, as a
canonical isomorphism of `D(B)`:

`Lπ_!(Ω_{𝒪/A} ⊗_𝒪 M̲) ≅ L_{B/A} ⊗^𝐋_B M`.

`CommAlgCat.atiyahFirstVertexMooreIso` computes the vertex by the derived form of [Stacks,
Tag 08PT] as an extended Moore complex on the standard resolution,
`CommAlgCat.atiyahFirstVertexDiagramIso` and `CommAlgCat.atiyahMooreTensorIso` identify that with
`M[0] ⊗ L_{B/A}`, and `CommAlgCat.atiyahDisplayedObj₁TensorIso` with `L_{B/A} ⊗^𝐋_B M`. -/
def atiyahFirstVertexDisplayedIso :
    (polynomialAtiyahTriangle A B M).obj₁ ≅ atiyahDisplayedObj₁ A B M :=
  atiyahFirstVertexMooreIso A B M ≪≫
    DerivedCategory.Q.mapIso
        ((mooreCochainComplex (atiyahStandardCosimplicialObject A B)).mapIso
          (atiyahFirstVertexDiagramIso A B M)) ≪≫
      DerivedCategory.Q.mapIso (atiyahMooreTensorIso A B M ≪≫
        (StacksDraft.TorAmplitude.FaithfullyFlat.singleTensorLeftMapHomologicalComplexIso
          M (moduleLiftCotangentComplex A B)).symm) ≪≫
        (atiyahDisplayedObj₁TensorIso A B M).symm

/-- **Stacks 09DE, the Atiyah class of a module.** For a ring map `A → B` and a `B`-module `M`,
the Atiyah class of `M` is the morphism

`M ⟶ (L_{B/A} ⊗^𝐋_B M)[1]`

of the derived category of `B`-modules that is the last arrow of the distinguished triangle
(92.17.0.1) of [Stacks, Tag 09DD], obtained by applying `Lπ_!` of [Stacks, Tag 09CZ] to the
sequence of first principal parts `0 ⟶ Ω_{𝒪/A} ⊗_𝒪 M̲ ⟶ P¹_{𝒪/A}(M) ⟶ M̲ ⟶ 0` on `C_{B/A}`, with
its endpoints identified by `Lπ_!(M̲) = M` ([Stacks, Tag 08QE],
`CommAlgCat.polynomialAtiyahTriangleObj₃Iso`) and
`Lπ_!(Ω_{𝒪/A} ⊗_𝒪 M̲) = L_{B/A} ⊗^𝐋_B M` ([Stacks, Tag 08PT] and the flatness of the terms of
`L_{B/A}`, `CommAlgCat.atiyahFirstVertexDisplayedIso`). That it is the last arrow of the
displayed distinguished triangle is `CommAlgCat.atiyahDisplayedTriangle_distinguished`. -/
@[stacks 09DE "the Atiyah class M → (L_{B/A} ⊗^L_B M)[1] in D(B): the last arrow of the triangle \
  of 09DD, its endpoints identified canonically by 08PT and 08QE"]
def atiyahClass :
    (DerivedCategory.singleFunctor (ModuleCat.{u + 1} (ULift.{u + 1} (B : Type u))) 0).obj M ⟶
      (atiyahDisplayedObj₁ A B M)⟦(1 : ℤ)⟧ :=
  polynomialAtiyahClassOfIso A B M (atiyahDisplayedObj₁ A B M)
    ((DerivedCategory.singleFunctor (ModuleCat.{u + 1} (ULift.{u + 1} (B : Type u))) 0).obj M)
    (atiyahFirstVertexDisplayedIso A B M) (polynomialAtiyahTriangleObj₃Iso A B M)

/-- **Stacks 09DD/09DE.** The displayed triangle

`L_{B/A} ⊗^𝐋_B M ⟶ Lπ_!(P¹_{𝒪/A}(M)) ⟶ M ⟶ (L_{B/A} ⊗^𝐋_B M)[1]`

of (92.17.0.1), whose last arrow is the Atiyah class `CommAlgCat.atiyahClass`, is
distinguished in `D(B)`. -/
@[stacks 09DD "the displayed triangle in D(B), its endpoints identified canonically and its last \
  arrow the Atiyah class"]
theorem atiyahDisplayedTriangle_distinguished :
    Triangle.mk ((atiyahFirstVertexDisplayedIso A B M).inv ≫ (polynomialAtiyahTriangle A B M).mor₁)
        ((polynomialAtiyahTriangle A B M).mor₂ ≫ (polynomialAtiyahTriangleObj₃Iso A B M).hom)
        (atiyahClass A B M) ∈ distinguishedTriangles :=
  polynomialAtiyahClassOfIso_mem_distinguished A B M _ _ _ _

end CommAlgCat

end
