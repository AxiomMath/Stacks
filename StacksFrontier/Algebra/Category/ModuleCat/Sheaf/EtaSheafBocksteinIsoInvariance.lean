module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheafBockstein

/-!
# The Bockstein complex of Tag 0GT8 is invariant under isomorphism

Let `X` be a ringed space and `ι : I ⟶ O_X` an invertible ideal subsheaf.  The Bockstein complex
`H^•(M/I)` of an object `M` of `D(O_X)` has terms `H^i(M ⊗^L I^i/I^{i+1})` and the Bockstein
operators as differentials.  An isomorphism `M ≅ M'` in `D(O_X)` induces an isomorphism
`H^•(M/I) ≅ H^•(M'/I)` of complexes: degreewise it is the cohomology of the isomorphism
`M ⊗^L I^i/I^{i+1} ≅ M' ⊗^L I^i/I^{i+1}`, and it commutes with the Bockstein operators because
`- ⊗^L A ⟶ - ⊗^L A` induced by `M ⟶ M'` commutes with the shift, so it is a morphism between the
images of the successive-power triangle, and connecting maps are natural in morphisms of
triangles.

## Main definitions

* `Stacks.IdealTorsion.ReductionDerived.bocksteinComplexMapIso`: the isomorphism
  `H^•(M/I) ≅ H^•(M'/I)` induced by an isomorphism `M ≅ M'`.

## Main results

* `Stacks.IdealTorsion.ReductionDerived.bocksteinOperator_naturality`: the Bockstein operator is
  natural in `M`.
* `Stacks.IdealTorsion.ReductionDerived.bocksteinComplexMapIso_hom_f`: the components of the
  induced isomorphism.

## References

* [Stacks Project, Tag 0GT8](https://stacks.math.columbia.edu/tag/0GT8)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

open Stacks.DerivedTensor.RingedSite (canonicalDerivedTensorProduct)

universe u

namespace Stacks.IdealTorsion.ReductionDerived

open Stacks.IdealTorsion.Bockstein

variable (X : RingedSpace.{u, u})

local notation "Oₓ" => (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)
local notation "𝒪" => SheafOfModules.unit Oₓ

/-- **The Bockstein operator is natural along isomorphisms in `D(O_X)`.**  An isomorphism
`e : M ≅ M'` induces `M ⊗^L A ≅ M' ⊗^L A`, which commutes with the shift, hence maps the image of
the successive-power triangle under `M ⊗^L -` to its image under `M' ⊗^L -`; the connecting maps
of the two long exact cohomology sequences are intertwined. -/
public theorem bocksteinOperator_naturality [HasDerivedCategory (SheafOfModules.{u} Oₓ)]
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)).property I]
    {M M' : DerivedCategory (SheafOfModules.{u} Oₓ)} (e : M ≅ M') (i : ℤ) :
    bocksteinOperator X I ι M i ≫
        (DerivedCategory.homologyFunctor (SheafOfModules.{u} Oₓ) (i + 1)).map
          (((canonicalDerivedTensorProduct X.sheaf).tensor.map e.hom).app
            ((DerivedCategory.singleFunctor (SheafOfModules.{u} Oₓ) 0).obj
              (powerQuotient X I ι (i + 1)))) =
      (DerivedCategory.homologyFunctor (SheafOfModules.{u} Oₓ) i).map
          (((canonicalDerivedTensorProduct X.sheaf).tensor.map e.hom).app
            ((DerivedCategory.singleFunctor (SheafOfModules.{u} Oₓ) 0).obj
              (powerQuotient X I ι i))) ≫
        bocksteinOperator X I ι M' i := by
  let := (canonicalDerivedTensorProduct X.sheaf).commShift_right M
  let := (canonicalDerivedTensorProduct X.sheaf).commShift_right M'
  let : NatTrans.CommShift ((canonicalDerivedTensorProduct X.sheaf).tensor.mapIso e).hom ℤ :=
    (canonicalDerivedTensorProduct X.sheaf).commShift₂.commShift_map e.hom
  let φ := ((Functor.mapTriangleIso ((canonicalDerivedTensorProduct X.sheaf).tensor.mapIso e)
    ).app (powerQuotientShortExact X I ι i).singleTriangle).hom
  exact ((DerivedCategory.homologyFunctor (SheafOfModules.{u} Oₓ) 0).homologySequenceδ_naturality
    φ i (i + 1) rfl).symm

/-- **The isomorphism of Bockstein complexes induced by an isomorphism in `D(O_X)`.**  In degree
`i` it is the cohomology in degree `i` of `e ⊗^L I^i/I^{i+1}`. -/
public noncomputable def bocksteinComplexMapIso [HasDerivedCategory (SheafOfModules.{u} Oₓ)]
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)).property I]
    {M M' : DerivedCategory (SheafOfModules.{u} Oₓ)} (e : M ≅ M') :
    bocksteinComplex X I ι M ≅ bocksteinComplex X I ι M' :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => (DerivedCategory.homologyFunctor (SheafOfModules.{u} Oₓ) i).mapIso
      (((canonicalDerivedTensorProduct X.sheaf).tensor.mapIso e).app
        ((DerivedCategory.singleFunctor (SheafOfModules.{u} Oₓ) 0).obj (powerQuotient X I ι i))))
    (by
      rintro i j rfl
      rw [bocksteinComplex_d, bocksteinComplex_d]
      exact (bocksteinOperator_naturality X I ι e i).symm)

/-- The degree-`i` component of `bocksteinComplexMapIso` is the cohomology of
`e ⊗^L I^i/I^{i+1}`. -/
@[simp] public theorem bocksteinComplexMapIso_hom_f [HasDerivedCategory (SheafOfModules.{u} Oₓ)]
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)).property I]
    {M M' : DerivedCategory (SheafOfModules.{u} Oₓ)} (e : M ≅ M') (i : ℤ) :
    (bocksteinComplexMapIso X I ι e).hom.f i =
      (DerivedCategory.homologyFunctor (SheafOfModules.{u} Oₓ) i).map
        (((canonicalDerivedTensorProduct X.sheaf).tensor.map e.hom).app
          ((DerivedCategory.singleFunctor (SheafOfModules.{u} Oₓ) 0).obj
            (powerQuotient X I ι i))) := rfl

end Stacks.IdealTorsion.ReductionDerived

end
