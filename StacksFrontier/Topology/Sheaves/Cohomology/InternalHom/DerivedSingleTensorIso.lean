module

public import StacksFrontier.Homology.KFlat.BifunctorSingleBothFactors
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorKFlatOneSided

/-!
# The derived tensor product of two modules in degree zero, when one of them is flat

Let `O` be a sheaf of commutative rings on a ringed site and `M`, `N` two sheaves of `O`-modules
with `M` flat.  Then

`M[0] ⊗^𝐋 N[0] ≅ (M ⊗_O N)[0]`

in `D(Mod(O))`, for the derived tensor product of [Stacks, Tag 0FPB].  This is the
identification that carries a statement about *sheaves* of modules into the derived category,
and it is the transport the off-diagonal terms of the implication `(2) ⟹ (1)` of [Stacks, Tag
0FPG] need: a retract between sheaves of modules becomes a retract in `D(𝒪_X)`.

Flatness of the **first** argument only is assumed, and it is needed: without it the statement
is false — `ℤ/2 ⊗^𝐋 ℤ/2` over `ℤ` has nonvanishing `Tor₁`, so its degree `-1` cohomology does not
vanish and it is not a module in degree zero.  The second argument is arbitrary.

## Main definitions

* `Stacks.SheafOfModules.DerivedMonoidal.tensorObjSingleIso`: the identification at the level of
  *complexes*, `Tot(M[0] ⊗ N[0]) ≅ (M ⊗_O N)[0]`, with no flatness at all.
* `Stacks.SheafOfModules.DerivedMonoidal.derivedTensorSingleIso`: the identification in
  `D(Mod(O))`, for `M` flat.
* `Stacks.Cohomology.MonoidalDerived.derivedTensorSingleIso`: the same on a ringed space.

## Implementation notes

Both halves are composites of existing identifications.  At the level of complexes the double
complex attached to `M[0]` and `N[0]` is concentrated in the spot `(0, 0)`, which is
`CochainComplex.KFlatBifunctor.mapBifunctorSingleBothIso`; the monoidal structure of `Complexes O`
has `HomologicalComplex.mapBifunctor` of `curriedTensor (Mod O)` as its tensor product on the nose,
so the generic statement applies with no transport.  Passing to the derived category is the
one-sided K-flat comparison `CochainComplex.KFlatMonoidal.derivedTensorLeftKFlatIso`, whose
hypothesis is K-flatness of the *first* argument only and which
`Stacks.SheafOfModules.KFlatResolution.kFlat_single_of_isFlat` supplies from flatness of `M`;
`DerivedCategory.Q` of the complex-level identification finishes it.

A ringed space is a ringed site and `Stacks.Cohomology.MonoidalDerived`
`.derivedCategoryMonoidalCategory X` is the ringed-site structure `derivedMonoidal X.sheaf` at
the site of opens of `X`, so the ringed-space statement is a definitional specialisation, the
same bridge `isZero_derivedTensor_of_isZero_tensor_of_isFlat_left` uses.

## References

* [Stacks Project, Tag 0FPB](https://stacks.math.columbia.edu/tag/0FPB) — the derived tensor
  product on `D(𝒪_X)`.
* [Stacks Project, Tag 0FPG](https://stacks.math.columbia.edu/tag/0FPG) — the implication
  `(2) ⟹ (1)`, which consumes this transport.
* [Stacks Project, Tag 06YN](https://stacks.math.columbia.edu/tag/06YN) — K-flat complexes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open Stacks.SheafOfModules.DerivedMonoidal

universe u d

namespace Stacks.SheafOfModules.DerivedMonoidal

attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
  CochainComplex.symmetricCategory

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
variable [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The total tensor product of two modules placed in degree zero is their tensor product
placed in degree zero**, with no flatness hypothesis.  The double complex is concentrated in the
spot `(0, 0)`, which is `CochainComplex.KFlatBifunctor.mapBifunctorSingleBothIso`.

This is the isomorphism of which `isZero_tensorObj_single_of_isZero` is the vanishing
consequence. -/
public def tensorObjSingleIso (M N : Mod R) :
    MonoidalCategory.tensorObj (C := Complexes R)
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj M)
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj N) ≅
      (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
        (MonoidalCategory.tensorObj (C := Mod R) M N) :=
  CochainComplex.KFlatBifunctor.mapBifunctorSingleBothIso
    (MonoidalCategory.curriedTensor (Mod R)) M N

variable [HasDerivedCategory.{d} (Mod R)]

/-- **The derived tensor product of two modules in degree zero, the first one flat, is their
tensor product in degree zero**, on a ringed site.

`M[0]` is K-flat because `M` is flat, so the one-sided comparison
`CochainComplex.KFlatMonoidal.derivedTensorLeftKFlatIso` identifies `M[0] ⊗^𝐋 N[0]` with
`Q(Tot(M[0] ⊗ N[0]))`, and `Q` of `tensorObjSingleIso` identifies that with `(M ⊗_O N)[0]`.
Nothing is assumed of `N`. -/
public def derivedTensorSingleIso (M N : Mod R)
    (hM : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R) M) :
    letI := derivedMonoidal R
    MonoidalCategory.tensorObj
        ((DerivedCategory.singleFunctor (Mod R) 0).obj M)
        ((DerivedCategory.singleFunctor (Mod R) 0).obj N) ≅
      (DerivedCategory.singleFunctor (Mod R) 0).obj
        (MonoidalCategory.tensorObj (C := Mod R) M N) :=
  letI := derivedMonoidal R
  CochainComplex.KFlatMonoidal.derivedTensorLeftKFlatIso (Mod R) (exists_kFlat_resolution R)
      (Stacks.SheafOfModules.KFlatResolution.kFlat_single_of_isFlat R M hM 0)
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj N) ≪≫
    (DerivedCategory.Q (C := Mod R)).mapIso (tensorObjSingleIso R M N)

end Stacks.SheafOfModules.DerivedMonoidal

namespace Stacks.Cohomology.MonoidalDerived

open AlgebraicGeometry Stacks.SheafOfModules.DerivedMonoidal

/-- **The derived tensor product of two modules in degree zero, the first one flat, is their
tensor product in degree zero**, on a ringed space, for the derived tensor product of Stacks
0FPB.

A ringed space is a ringed site and `derivedCategoryMonoidalCategory X` is the ringed-site
structure `derivedMonoidal X.sheaf` at the site of opens of `X`, so nothing is transported. -/
public def derivedTensorSingleIso (X : RingedSpace.{u, u})
    [HasDerivedCategory.{d} (Mod X.sheaf)] (M N : Mod X.sheaf)
    (hM : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) M) :
    letI := derivedCategoryMonoidalCategory.{u, d} X
    MonoidalCategory.tensorObj
        ((DerivedCategory.singleFunctor (Mod X.sheaf) 0).obj M)
        ((DerivedCategory.singleFunctor (Mod X.sheaf) 0).obj N) ≅
      (DerivedCategory.singleFunctor (Mod X.sheaf) 0).obj
        (letI := SheafOfModules.monoidalCategorySheafTensor X.sheaf
         MonoidalCategory.tensorObj (C := Mod X.sheaf) M N) :=
  Stacks.SheafOfModules.DerivedMonoidal.derivedTensorSingleIso X.sheaf M N hM

end Stacks.Cohomology.MonoidalDerived

end
