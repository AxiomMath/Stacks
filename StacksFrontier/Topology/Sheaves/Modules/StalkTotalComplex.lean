module

public import StacksFrontier.Homology.TotalComplexTransport
public import StacksFrontier.Topology.Sheaves.Modules.StalkAcyclic
public import StacksFrontier.Topology.Sheaves.Modules.StalkCokernel
public import StacksFrontier.Topology.Sheaves.Modules.StalkTensor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.KFlatComplexesDefinition

/-!
# The module stalk functor commutes with a total complex

Let `𝒪` be a sheaf of rings on a topological space `X` and let `x : X`. The stalk functor
`AlgebraicGeometry.SheafOfModules.stalkFunctor 𝒪 x : Mod(𝒪) ⥤ ModuleCat 𝒪_x` preserves all
colimits (Stacks 01AH, `stalkFunctor_preservesColimits`). This file records the consequence
that the stalk criterion for K-flatness (Stacks 06YB) rests on: the stalk functor carries the
total complex `Tot(F(K, L))` of a bifunctor to the total complex of the transported bifunctor,
by `CategoryTheory.Functor.mapBifunctorTotalIso`.

Both directions of Stacks 06YB reduce to that single statement. In the direction
"stalkwise K-flat implies K-flat", one tests acyclicity of `Tot(F ⊗_𝒪 K)` stalkwise with
`acyclic_iff_forall_stalk_acyclic` and must recognise the stalk of the total complex as the
total complex of the stalks. In the direction "K-flat implies stalkwise K-flat", one feeds a
sheaf whose stalk at `x` is a prescribed acyclic complex of `𝒪_x`-modules and must make the
same identification. Neither direction can be stated, let alone proved, without it.

## Main results

* `AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesAntidiagonalCoproducts`: the stalk
  functor preserves exactly the coproducts that occur in a total complex over `ℤ`.
* `AlgebraicGeometry.SheafOfModules.stalkTotalComplexIso`: the stalk functor commutes with
  the total complex of a bifunctor which it transports.

## Implementation notes

The colimit-preservation hypothesis of `Functor.mapBifunctorTotalIso` is about shape
categories `Discrete ↥(ComplexShape.π _ _ _ ⁻¹' {n})`, whose object and morphism types live in
`Type 0`, while `stalkFunctor_preservesColimits` is `PreservesColimitsOfSize` at the ambient
universes of `Mod(𝒪)` and `ModuleCat 𝒪_x`. Instance search does not bridge the two: a
`PreservesColimitsOfSize.{u, u}` instance is not seen as supplying
`PreservesColimitsOfShape (Discrete T)` for `T : Type 0`, because the shrinking step
`preservesColimitsOfSize_shrink` is a lemma and not an instance. So the shrunk form is seated
here as a named declaration, and the antidiagonal form is derived from it; attempting to let
synthesis find either one directly fails with `failed to synthesize`.

`stalkTotalComplexIso` leaves the target bifunctor and the comparison `ε` as arguments rather
than fixing them to the tensor product of `Stacks.SheafOfModules.Tensor.sheafTensor`. That is
  deliberate: the
comparison for the tensor product is the stalk-of-a-tensor-product isomorphism
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso`, which is stated over the
  `CommRingCat`-valued stalk of the
structure sheaf, whereas `stalkFunctor` takes its modules over the `RingCat`-valued stalk.
Those two rings are isomorphic but not equal — the comparison is
`SemilinearStalk.commStalkRingEquiv`, and the compatibility of the two scalar actions along it
is `SemilinearStalk.comm_smul_eq` — so supplying `ε` for the tensor product additionally
requires transporting a `TensorProduct` along that ring isomorphism. Stating the general form
here separates the plumbing from that transport.

**That transport has been done.** `Stacks.SheafOfModules.KFlatStalkCriterion.stalkTensorIso`
is `ε` for `Stacks.SheafOfModules.Tensor.sheafTensor`, with its two naturality statements
`stalkTensorIso_naturality_left` and `stalkTensorIso_naturality_right`, and
`Stacks.SheafOfModules.KFlatStalkCriterion.stalkTensorComplexIso` is this file's
`stalkTotalComplexIso` instantiated at them: the stalk of a total tensor complex *is* the total
tensor complex of the stalks, for arbitrary complexes of sheaves of modules. Both live in
`StacksFrontier.Topology.Sheaves.Cohomology.KFlat.StalkCriterion`.

## References

* [Stacks Project, Tag 01AH](https://stacks.math.columbia.edu/tag/01AH)
* [Stacks Project, Tag 06YB](https://stacks.math.columbia.edu/tag/06YB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

noncomputable section

namespace AlgebraicGeometry.SheafOfModules

variable {X : TopCat.{u}}
  (𝒪 : CategoryTheory.Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (x : X)

/-- The stalk functor preserves the coproducts occurring in the total complex of a double
cochain complex over `ℤ`: those indexed by an antidiagonal
`ComplexShape.π (up ℤ) (up ℤ) (up ℤ) ⁻¹' {n}`.

This is the hypothesis of `CategoryTheory.Functor.mapBifunctorTotalIso`, so this lemma is what
makes the total complex transport along the stalk functor at all. -/
public lemma stalkFunctor_preservesAntidiagonalCoproducts (n : ℤ) :
    PreservesColimitsOfShape
      (Discrete ↥(ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) ⁻¹' {n}))
      (stalkFunctor 𝒪 x) :=
  let := stalkFunctor_preservesSmallestColimits 𝒪 x
  inferInstance

/-- **The stalk functor commutes with a total complex.** If the stalk functor at `x` carries a
bifunctor `F` on sheaves of `𝒪`-modules to a bifunctor `F'` on `𝒪_x`-modules — that is, if
there are isomorphisms `ε : (F(M, N))_x ≅ F'(M_x, N_x)` natural in `M` and in `N` — then it
carries the total complex of `F` to the total complex of `F'`:

  `(Tot(F(K, L)))_x ≅ Tot(F'(K_x, L_x))`.

For `F` the tensor product of sheaves of modules and `F'` the tensor product of modules over
the stalk ring, this is the identification on which the stalk criterion for K-flatness
(Stacks 06YB) rests, in both directions. -/
public noncomputable def stalkTotalComplexIso
    (F : _root_.SheafOfModules.{u} 𝒪 ⥤ _root_.SheafOfModules.{u} 𝒪 ⥤ _root_.SheafOfModules.{u} 𝒪)
    (F' : ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u}) (X := X) 𝒪.obj x) ⥤
      ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u}) (X := X) 𝒪.obj x) ⥤
      ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u}) (X := X) 𝒪.obj x))
    [F.PreservesZeroMorphisms] [∀ M, (F.obj M).PreservesZeroMorphisms]
    [F'.PreservesZeroMorphisms] [∀ M, (F'.obj M).PreservesZeroMorphisms]
    (ε : ∀ (M N : _root_.SheafOfModules.{u} 𝒪),
      (stalkFunctor 𝒪 x).obj ((F.obj M).obj N) ≅
        (F'.obj ((stalkFunctor 𝒪 x).obj M)).obj ((stalkFunctor 𝒪 x).obj N))
    (hε₁ : ∀ {M M' : _root_.SheafOfModules.{u} 𝒪} (f : M ⟶ M') (N : _root_.SheafOfModules.{u} 𝒪),
      (stalkFunctor 𝒪 x).map ((F.map f).app N) ≫ (ε M' N).hom =
        (ε M N).hom ≫ (F'.map ((stalkFunctor 𝒪 x).map f)).app ((stalkFunctor 𝒪 x).obj N))
    (hε₂ : ∀ (M : _root_.SheafOfModules.{u} 𝒪) {N N' : _root_.SheafOfModules.{u} 𝒪} (g : N ⟶ N'),
      (stalkFunctor 𝒪 x).map ((F.obj M).map g) ≫ (ε M N').hom =
        (ε M N).hom ≫ (F'.obj ((stalkFunctor 𝒪 x).obj M)).map ((stalkFunctor 𝒪 x).map g))
    (K L : CochainComplex (_root_.SheafOfModules.{u} 𝒪) ℤ)
    [HomologicalComplex.HasMapBifunctor K L F (ComplexShape.up ℤ)]
    [HomologicalComplex.HasMapBifunctor
      (((stalkFunctor 𝒪 x).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
      (((stalkFunctor 𝒪 x).mapHomologicalComplex (ComplexShape.up ℤ)).obj L) F'
      (ComplexShape.up ℤ)]
    [HomologicalComplex₂.HasTotal (HomologicalComplex₂.mapBicomplex (stalkFunctor 𝒪 x)
      (((F.mapBifunctorHomologicalComplex (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)).obj K).obj L)) (ComplexShape.up ℤ)] :
    ((stalkFunctor 𝒪 x).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (HomologicalComplex.mapBifunctor K L F (ComplexShape.up ℤ)) ≅
      HomologicalComplex.mapBifunctor
        (((stalkFunctor 𝒪 x).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
        (((stalkFunctor 𝒪 x).mapHomologicalComplex (ComplexShape.up ℤ)).obj L) F'
        (ComplexShape.up ℤ) :=
  letI := fun n : ℤ => stalkFunctor_preservesAntidiagonalCoproducts 𝒪 x n
  CategoryTheory.Functor.mapBifunctorTotalIso F F' (stalkFunctor 𝒪 x) (stalkFunctor 𝒪 x)
    (stalkFunctor 𝒪 x) ε (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
    hε₁ hε₂ K L

end AlgebraicGeometry.SheafOfModules

end

end
