module

public import StacksFrontier.AlgebraicGeometry.Modules.AlternatingCechModuleBaseChangeComp
public import StacksFrontier.AlgebraicGeometry.Perfect.BaseAlternatingCechBaseChangeDegreewise

/-!
# The `A`-linear Čech model as a functor of the module

`Stacks.AlgebraicGeometry.ProperFlatGlobalSections.baseAlternatingCechComplex f U hU G` depends
on the `𝒪_X`-module `G`, and the `ℕ`-indexed alternating Čech complex of `A`-modules is
functorial in that module by `Stacks.Cech.alternatingCechModuleComplexMapIso`. This file
transports that functoriality to the `ℤ`-indexed `A`-linear model, and pins the transport in each
nonnegative degree.

The transport is needed because a tower of two base changes compares two different modules on the
bottom scheme: the composite comparison is about `(g' ≫ g)^* F`, while the two-step route lands
in `g'^* (g^* F)`, and `AlgebraicGeometry.Scheme.Modules.pullbackComp` relates them. The
isomorphism of models built here is how the two `ℤ`-indexed Čech models are identified.

## Main definitions

* `Stacks.AlgebraicGeometry.ProperFlatGlobalSections.baseAlternatingCechComplexMapIso`: an
  isomorphism `G ≅ H` of `𝒪_X`-modules induces an isomorphism
  `baseAlternatingCechComplex f U hU G ≅ baseAlternatingCechComplex f U hU H` of the `ℤ`-indexed
  `A`-linear models.

## Main results

* `Stacks.DerivedIndexing.f_comp_extendMap_f_comp`: for a morphism `ψ` of `c`-indexed complexes,
  the extension by zero of `ψ` along an embedding `c ↪ c'`, flanked by two identifications of the
  extensions by zero with other `c'`-indexed complexes, has in a degree in the range of the
  embedding the component `ψ.f i` conjugated by the comparisons
  `HomologicalComplex.extendXIso`. Abstract: the embedding, the shapes, the category and the
  degree are arbitrary.
* `…ProperFlatGlobalSections.baseAlternatingCechComplexMapIso_hom_f_comp_XIso`: **in a
  nonnegative degree `m` the induced isomorphism of models is the degreewise morphism
  `Stacks.Cech.alternatingCechModuleObjMap`**, conjugated by the two degree isomorphisms
  `baseAlternatingCechComplexXIso`. This is the pinning in the shape of
  `baseAlternatingCechComplexBaseChangeIso_hom_f_comp_XIso`, and it is what makes an identity
  between composites involving this isomorphism checkable degreewise.

## Implementation notes

`Stacks.DerivedIndexing.f_comp_extendMap_f_comp` is the analogue of
`Stacks.DerivedIndexing.map_f_comp_mapExtendIso_inv_f_comp_extendMap_f_comp` with no functor
applied termwise, so the comparison `Stacks.DerivedIndexing.mapExtendIso` does not occur and only
three factors are matched. It is stated abstractly and applied in term position for the reason
recorded in `BaseAlternatingCechBaseChangeDegreewise.lean`: the model's identification with an
extension by zero is spelled with `ComplexShape.Embedding.extendFunctor`, Mathlib's degreewise
comparisons with `HomologicalComplex.extend`, and the two spellings are not reducibly equal, so a
goal mentioning both admits no rewriting at all. The whole three-fold composite is therefore
matched up to definitional equality, in term position, by a single `Eq.trans`.

Every proof argument appearing in a statement is supplied by a named theorem rather than by the
term `rfl`: `ComplexShape.embeddingUpNat_f` for `ComplexShape.embeddingUpNat.f m = (m : ℤ)`. See
the implementation notes of `BaseAlternatingCechBaseChangeDegreewise.lean`.

The file runs under `HasDerivedCategory.standard` at priority `10000`, as the files it builds on
do.

## References

* [Stacks Project, Tag 01XL](https://stacks.math.columbia.edu/tag/01XL)
* [Stacks Project, Tag 07VK](https://stacks.math.columbia.edu/tag/07VK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace Stacks.DerivedIndexing

/-- **The degreewise component, in a degree in the range of the embedding, of a transport of a
morphism of `c`-indexed complexes to `c'`-indexed complexes through two identifications with
extensions by zero.** The transport is a three-fold composite: an identification `a` of the
source with an extension by zero, the extension by zero of `ψ`, and an identification `b` of the
extension by zero of the target with the target. Read through a morphism `y` identifying the term
of `b`'s target with the term of `L` — the hypothesis `hy` — its component in the degree `e.f i`
is the component `ψ.f i`, precomposed with the component of `a` read through
`HomologicalComplex.extendXIso`.

This is `map_f_comp_mapExtendIso_inv_f_comp_extendMap_f_comp` with no functor applied termwise,
and is abstract for the same reason: in the application the two spellings
`HomologicalComplex.extend` and `ComplexShape.Embedding.extendFunctor` of an extension by zero
both occur and are not reducibly equal, so no rewriting can be done on the goal. -/
lemma f_comp_extendMap_f_comp {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
    {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] (e : c.Embedding c')
    {K L : HomologicalComplex C c} {B B' : HomologicalComplex C c'} (a : B ⟶ K.extend e)
    (ψ : K ⟶ L) (b : L.extend e ⟶ B') {i : ι} {i' : ι'} (h : e.f i = i')
    (y : B'.X i' ⟶ L.X i) (hy : b.f i' ≫ y = (L.extendXIso e h).hom) :
    (a.f i' ≫ (HomologicalComplex.extendMap ψ e).f i' ≫ b.f i') ≫ y =
      (a.f i' ≫ (K.extendXIso e h).hom) ≫ ψ.f i := by
  rw [HomologicalComplex.extendMap_f ψ e h]
  simp only [Category.assoc]
  rw [hy, Iso.inv_hom_id, Category.comp_id]

end Stacks.DerivedIndexing

namespace Stacks.AlgebraicGeometry.ProperFlatGlobalSections

attribute [local instance 10000] HasDerivedCategory.standard

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
  {I : Type u} (U : I → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i) {G H : X.Modules}

/-- **The `ℤ`-indexed `A`-linear Čech model is functorial in the module.** An isomorphism
`t : G ≅ H` of `𝒪_X`-modules induces an isomorphism of the `A`-linear alternating Čech models of
a family `U` of opens.

It is the functoriality `Stacks.Cech.alternatingCechModuleComplexMapIso` of the `ℕ`-indexed
alternating Čech complex of `A`-modules, extended by zero along `ℕ ↪ ℤ` and read through the two
identifications `baseAlternatingCechComplexIsoExtend` of the models with those extensions. -/
def baseAlternatingCechComplexMapIso (t : G ≅ H) :
    baseAlternatingCechComplex f U hU G ≅ baseAlternatingCechComplex f U hU H :=
  baseAlternatingCechComplexIsoExtend f U hU G ≪≫
    (ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} A)).mapIso
      (Stacks.Cech.alternatingCechModuleComplexMapIso f U t) ≪≫
    (baseAlternatingCechComplexIsoExtend f U hU H).symm

/-- **In a nonnegative degree `m` the isomorphism of models induced by `t : G ≅ H` is the
degreewise morphism `Stacks.Cech.alternatingCechModuleObjMap` of `t.hom`**, conjugated by the two
degree isomorphisms `baseAlternatingCechComplexXIso` of the models.

This is the pinning in the shape of
`baseAlternatingCechComplexBaseChangeIso_hom_f_comp_XIso`: the two
`baseAlternatingCechComplexIsoExtend` factors contribute the two degree isomorphisms, and the
comparisons `HomologicalComplex.extendXIso` introduced by the extension by zero of the middle
factor cancel. -/
theorem baseAlternatingCechComplexMapIso_hom_f_comp_XIso (t : G ≅ H) (m : ℕ) :
    (baseAlternatingCechComplexMapIso f U hU t).hom.f (m : ℤ) ≫
        (baseAlternatingCechComplexXIso f U hU H m).hom =
      (baseAlternatingCechComplexXIso f U hU G m).hom ≫
        Stacks.Cech.alternatingCechModuleObjMap f U t.hom m := by
  have hA := baseAlternatingCechComplexIsoExtend_hom_f_comp_extendXIso f U hU G m
  have hA' := baseAlternatingCechComplexIsoExtend_hom_f_comp_extendXIso f U hU H m
  have key : (baseAlternatingCechComplexIsoExtend f U hU H).inv.f (m : ℤ) ≫
        (baseAlternatingCechComplexXIso f U hU H m).hom =
      ((Stacks.Cech.alternatingCechModuleComplex f U H).extendXIso ComplexShape.embeddingUpNat
        (ComplexShape.embeddingUpNat_f m)).hom :=
    (Iso.inv_comp_eq (HomologicalComplex.Hom.isoApp
      (baseAlternatingCechComplexIsoExtend f U hU H) (m : ℤ))).2 hA'.symm
  refine Eq.trans (Stacks.DerivedIndexing.f_comp_extendMap_f_comp
      ComplexShape.embeddingUpNat (baseAlternatingCechComplexIsoExtend f U hU G).hom
      (Stacks.Cech.alternatingCechModuleComplexMap f U t.hom)
      (baseAlternatingCechComplexIsoExtend f U hU H).inv
      (ComplexShape.embeddingUpNat_f m)
      (baseAlternatingCechComplexXIso f U hU H m).hom key) ?_
  exact congrArg (fun z => z ≫ Stacks.Cech.alternatingCechModuleObjMap f U t.hom m) hA

end Stacks.AlgebraicGeometry.ProperFlatGlobalSections

end
