module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorComparison

/-!
# The naive cup product on a ringed space

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces and let `𝒦^•` and `ℳ^•` be
complexes of `𝒪_X`-modules.  The *naive cup product* is the map of complexes of
`𝒪_Y`-modules

`Tot(f_*𝒦^• ⊗_{𝒪_Y} f_*ℳ^•) ⟶ f_*Tot(𝒦^• ⊗_{𝒪_X} ℳ^•)`

adjoint, under `f^* ⊣ f_*` of Stacks 0096, to the comparison
`f^*Tot(f_*𝒦^• ⊗_{𝒪_Y} f_*ℳ^•) ≅ Tot(f^*f_*𝒦^• ⊗_{𝒪_X} f^*f_*ℳ^•)` of Stacks 01CD followed
by the ordinary counit `f^*f_* ⟶ id` in each of the two tensor factors.

## Main definitions

* `Stacks.Cohomology.NaiveCupProductOnRingedSpaces.pushforwardComplex`: the degreewise
  pushforward of cochain complexes of modules.
* `Stacks.Cohomology.NaiveCupProductOnRingedSpaces.complexAdjunction`: the adjunction
  `f^* ⊣ f_*` on cochain complexes of modules.
* `Stacks.Cohomology.NaiveCupProductOnRingedSpaces.naiveCupProductTranspose`: the map of which
  the naive cup product is the adjoint transpose.
* `Stacks.Cohomology.NaiveCupProductOnRingedSpaces.naiveCupProduct`: **the naive cup product**.

## Main results

* `Stacks.Cohomology.NaiveCupProductOnRingedSpaces.pullbackComplex_naiveCupProduct_counit`: the
  square identifying the naive cup product against the ordinary counits, which is what the
  source offers as its definition.
* `Stacks.Cohomology.NaiveCupProductOnRingedSpaces.naiveCupProduct_eq_unit_comp`: the naive cup
  product written through the unit of `f^* ⊣ f_*`.

## Implementation notes

*Why the adjoint transpose is the definition.*  Degreewise the naive cup product is the
two-sided comparison `f_*ℱ ⊗_{𝒪_Y} f_*𝒢 ⟶ f_*(ℱ ⊗_{𝒪_X} 𝒢)` on each summand of each total
degree.  Assembling those into a map of complexes would ask for the total complex of the
tensor double complex pushed forward termwise, which is not available: `f_*` does not preserve
the coproducts occurring in a total degree.  The adjoint transpose needs none of that, and
nothing is lost, because `pullbackComplex_naiveCupProduct_counit` — the square the source
itself offers as the definition — pins the map down uniquely, being the statement that it is
that transpose.

No boundedness, flatness or quasi-coherence hypothesis is imposed on `𝒦^•` or `ℳ^•`: the
source imposes none, and no step here needs one.

*The spelling of the categories of modules.*  The two tensor-product developments and the
pullback–pushforward development name the structure sheaf of a ringed space differently, by
`Stacks.SheafOfModules.Tensor.ringSheaf` and by `structureSheafRing`.  The
two are the same sheaf of rings by `rfl`, and the statements below mix them, so the first is
unfolded at `implicit` transparency here exactly as in
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorComparison`; the same
is done for the two retyped functors of `StacksFrontier.Homology.KFlat.Pullback`.

## References

* [Stacks Project, Tag 0FP3](https://stacks.math.columbia.edu/tag/0FP3)
* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped CategoryTheory.Prod

namespace Stacks.Cohomology.NaiveCupProductOnRingedSpaces

universe u

attribute [local instance]
  Stacks.Cohomology.DerivedPullbackTensor.modulePullback_preservesAntidiagonalCoproducts

attribute [local implicit_reducible] structureSheafRing
  StacksDraft.KFlat.modulePullback StacksDraft.KFlat.modulePushforward

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-! ## Pushforward of complexes and the adjunction on complexes -/

/-- The degreewise pushforward `f_*` of cochain complexes of modules along a morphism of
ringed spaces, at the spelling of the tensor product of sheaves of modules. -/
abbrev pushforwardComplex :
    CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) ℤ ⥤
      CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ :=
  (StacksDraft.KFlat.modulePushforward f).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The adjunction `f^* ⊣ f_*` on cochain complexes of modules, induced degreewise by the
adjunction of Stacks 0096.  Its unit and counit are those of Stacks 0096 in each degree. -/
def complexAdjunction :
    Stacks.Cohomology.DerivedPullbackTensor.pullbackComplex f ⊣ pushforwardComplex f :=
  Adjunction.mapHomologicalComplexAdjunction
    (RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction f) (ComplexShape.up ℤ)

/-- The counit of `f^* ⊣ f_*` on complexes is the counit of Stacks 0096 in each degree. -/
lemma complexAdjunction_counit_app_f
    (K : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) ℤ)
    (n : ℤ) :
    ((complexAdjunction f).counit.app K).f n =
      (RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction f).counit.app (K.X n) :=
  rfl

/-! ## The naive cup product -/

variable (K M : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) ℤ)

/-- The map `f^*Tot(f_*𝒦^• ⊗_{𝒪_Y} f_*ℳ^•) ⟶ Tot(𝒦^• ⊗_{𝒪_X} ℳ^•)` of which the naive cup
product is the adjoint transpose: the comparison of total tensor complexes of Stacks 01CD
followed by the ordinary counit `f^*f_* ⟶ id` in each tensor factor. -/
def naiveCupProductTranspose :
    (Stacks.Cohomology.DerivedPullbackTensor.pullbackComplex f).obj
        ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
            (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf)).obj
          ((pushforwardComplex f).obj K, (pushforwardComplex f).obj M)) ⟶
      (Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
        (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf)).obj (K, M) :=
  (Stacks.Cohomology.DerivedPullbackTensor.pullbackTensorComplexNatIso f).hom.app
      ((pushforwardComplex f).obj K, (pushforwardComplex f).obj M) ≫
    (Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
        (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf)).map
      ((complexAdjunction f).counit.app K ×ₘ (complexAdjunction f).counit.app M)

/-- **The naive cup product** `Tot(f_*𝒦^• ⊗_{𝒪_Y} f_*ℳ^•) ⟶ f_*Tot(𝒦^• ⊗_{𝒪_X} ℳ^•)`, for
arbitrary complexes `𝒦^•`, `ℳ^•` of `𝒪_X`-modules: the map adjoint, under `f^* ⊣ f_*` of
Stacks 0096, to the comparison of total tensor complexes of Stacks 01CD followed by the
ordinary counit `f^*f_* ⟶ id` in each of the two tensor factors. -/
def naiveCupProduct :
    (Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
        (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf)).obj
        ((pushforwardComplex f).obj K, (pushforwardComplex f).obj M) ⟶
      (pushforwardComplex f).obj
        ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
          (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf)).obj (K, M)) :=
  (complexAdjunction f).homEquiv _ _ (naiveCupProductTranspose f K M)

/-- The naive cup product written through the unit of `f^* ⊣ f_*`. -/
lemma naiveCupProduct_eq_unit_comp :
    naiveCupProduct f K M =
      (complexAdjunction f).unit.app
          ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
            (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf)).obj
            ((pushforwardComplex f).obj K, (pushforwardComplex f).obj M)) ≫
        (pushforwardComplex f).map (naiveCupProductTranspose f K M) :=
  Adjunction.homEquiv_unit _ _ _ _

/-- **The square identifying the naive cup product against the ordinary counits**, which the
Stacks project says may be viewed as its definition: `f^*` of the naive cup product followed
by the counit `f^*f_*Tot(𝒦^• ⊗ ℳ^•) ⟶ Tot(𝒦^• ⊗ ℳ^•)` is the comparison of total tensor
complexes of Stacks 01CD followed by the counit in each tensor factor. -/
theorem pullbackComplex_naiveCupProduct_counit :
    (Stacks.Cohomology.DerivedPullbackTensor.pullbackComplex f).map (naiveCupProduct f K M) ≫
        (complexAdjunction f).counit.app
          ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
            (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf)).obj (K, M)) =
      (Stacks.Cohomology.DerivedPullbackTensor.pullbackTensorComplexNatIso f).hom.app
          ((pushforwardComplex f).obj K, (pushforwardComplex f).obj M) ≫
        (Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
            (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf)).map
          ((complexAdjunction f).counit.app K ×ₘ (complexAdjunction f).counit.app M) :=
  Equiv.symm_apply_apply ((complexAdjunction f).homEquiv _ _) (naiveCupProductTranspose f K M)

end Stacks.Cohomology.NaiveCupProductOnRingedSpaces

end
