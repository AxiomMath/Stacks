module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedConeDesc
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeDifferentialGradedModuleConeHomotopy
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GoodDifferentialGradedResolutionPairs
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GoodDifferentialGradedResolutionStep

/-!
# The inductive step of a flat resolution: the map to the target

Let `(C, O)` be a ringed site, let `A` be a sheaf of differential graded `O`-algebras, let `M` and
`P` be right differential graded `A`-modules and let `τ : P ⟶ M` be a homomorphism. The first
proof of Tag 0FSH builds the next stage of its tower as the twisted extension of `P` by the free
module on the sheaf of graded sets of boundary pairs of `τ`, and maps that stage to `M` by `τ` on
`P` and by the second component of a pair on the generator that pair names. This file builds that
map.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.primitiveFamily` is the family of homogeneous local
  sections of the shift down by one of `M` carried by the boundary pairs: the section attached to
  a local section of degree `n` is the second component of its degree-`n` pair.
* `SheafOfModules.DifferentialGradedModule.boundaryPairImageFamily` is the family of
  homogeneous local sections of `M` the boundary pairs carry through `τ`: the image under `τ` of
  the first component of a pair, which is the differential of its second component.
* `SheafOfModules.DifferentialGradedModule.stepHomotopy` is the degreewise family
  `A[S]^{n+1} ⟶ M^n` the primitives lift to, which is
  `SheafOfModules.DifferentialGradedModule.freeHomotopy` at that family.
* `SheafOfModules.DifferentialGradedModule.towerStepMap` is the resulting map to `M` from the
  twisted extension of `P` by the free module on the boundary pairs.

## Main results

* `SheafOfModules.DifferentialGradedModule.stepHomotopy_mul`: **the homotopy is right
  `A`-linear**, in the degree-shifted form the cone consumes.
* `SheafOfModules.DifferentialGradedModule.stepHomotopy_delta`: **the homotopy is a null-homotopy
  of `A[S] ⟶ P ⟶ M`.**
* `SheafOfModules.DifferentialGradedModule.stepHomotopy_generator` and
  `SheafOfModules.DifferentialGradedModule.d_boundaryPairPrimitive` are the two readings of the
  boundary-pair data the above computation needs: the homotopy sends the generator named by a
  pair to its second component, and the differential of `M` carries that second component to the
  image under `τ` of the first.
* `SheafOfModules.DifferentialGradedModule.twistedExtensionInclusion_towerStepMap`: **the map
  from the next stage of the tower restricts to `τ` on `P`**, so the tower it builds is a tower
  over `M`.

## Implementation notes

Neither the homotopy nor its two properties are built here. They are
`SheafOfModules.DifferentialGradedModule.freeHomotopy`, `freeHomotopy_mul` and
`freeHomotopy_delta` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/FreeDifferentialGradedModuleConeHomotopy.lean`,
which carry an arbitrary sheaf of graded sets and an arbitrary family of primitives; all this
file supplies is the two pieces of boundary-pair data they ask for -- the family of primitives
itself, and `d_boundaryPairPrimitive`, which says that the differential of a primitive is the
image under `τ` of the generator its pair names. Every statement therefore carries transports
along propositionally but not definitionally equal degrees, written through
`SheafOfModules.castHom` as everywhere in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/FreeGradedModule.lean`.

The right-hand side of the general null-homotopy identity is the degree-`n + 1` component of
`SheafOfModules.liftHom`, so `stepHomotopy_delta` has one step of its own: the graded
homomorphism underlying `A[S] ⟶ P ⟶ M` is the lift of `boundaryPairImageFamily`, which is
`SheafOfModules.freeGradedModule_hom_ext` on the generators.

## References

* [Stacks Project, Tag 0FSH](https://stacks.math.columbia.edu/tag/0FSH)
* [Stacks Project, Tag 0FSF](https://stacks.math.columbia.edu/tag/0FSF)
* [Stacks Project, Tag 0FS5](https://stacks.math.columbia.edu/tag/0FS5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

universe t m v u

namespace SheafOfModules.DifferentialGradedModule

open Stacks Stacks.SheafOfGradedSets

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})]
  [HasWeakSheafify J (Type m)]
  [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasSheafify J AddCommGrpCat.{m}]
  {Osharp : Sheaf J CommRingCat.{t}}
  {A : DifferentialGradedAlgebra.{t, m} (toRingCat J Osharp)}
  {M P : DifferentialGradedModule.{t, m, m} A}

/-! ### The family of primitives carried by the boundary pairs -/

/-- **The family of homogeneous generators of the shift down by one of `M` carried by the sheaf
of graded sets of boundary pairs**: the section attached to a local section of degree `n` is the
second component of the boundary pair of degree `n` that this local section carries, a section of
`M^{n-1}`, which is the degree-`n` piece of
`SheafOfModules.DifferentialGradedModule.gradedShiftDown M`. -/
noncomputable def primitiveFamily (τ : P ⟶ M) :
    GradedGeneratorFamily (boundaryPairs τ.toHomologicalComplex) (gradedShiftDown M) where
  app n V s _ := homSections (boundaryPairPrimitive τ.toHomologicalComplex n) V (s.pair n)
  naturality := by
    intro n V W f s _ _
    exact homSections_naturality (boundaryPairPrimitive τ.toHomologicalComplex n) f (s.pair n)

/-- The section the family of primitives attaches to a local section of degree `n`. -/
@[simp] theorem primitiveFamily_app (τ : P ⟶ M) (n : ℤ) (V : Cᵒᵖ)
    (s : (boundaryPairs τ.toHomologicalComplex).sheaf.obj.obj V)
    (hs : (boundaryPairs τ.toHomologicalComplex).HasDegree V s n) :
    (primitiveFamily τ).app n V s hs =
      homSections (boundaryPairPrimitive τ.toHomologicalComplex n) V (s.pair n) :=
  rfl

/-- **The differential of `M` carries the primitive attached to a local section of degree `j` to
the image under `τ` of the generator attached to it.** This is the defining condition of a
boundary pair, transported into the degree `(j - 1) + 1` in which the Leibniz rule of `M`
produces it. -/
theorem d_boundaryPairPrimitive (τ : P ⟶ M) (j : ℤ) (V : Cᵒᵖ)
    (s : (boundaryPairs τ.toHomologicalComplex).sheaf.obj.obj V)
    (hs : (boundaryPairs τ.toHomologicalComplex).HasDegree V s j) :
    homSections (M.complex.d (j - 1) ((j - 1) + 1)) V
        (homSections (boundaryPairPrimitive τ.toHomologicalComplex j) V (s.pair j)) =
      castHom (GradedModule.ofDifferentialGraded M).piece
        (degEqSubOneSucc j) V
        (((GradedModule.ofDifferentialGradedMap τ).app j).val.app V
          ((boundaryPairFamily τ).app j V s hs)) := by
  refine Eq.trans (castHom_homSections_d M.complex (j - 1)
    (degEqSubOneSucc j) V _).symm ?_
  exact congrArg (fun z => castHom M.complex.X (degEqSubOneSucc j) V z)
    (boundaryPairPrimitive_d τ.toHomologicalComplex j V (s.pair j))

/-! ### The homotopy and the map from the next stage of the tower -/

/-- **The family of homogeneous local sections of `M` the boundary pairs carry through `τ`**: the
image under `τ` of the first component of a degree-`n` pair, a section of `M^n`. By
`SheafOfModules.DifferentialGradedModule.d_boundaryPairPrimitive` it is the differential of the
family of primitives, which is the hypothesis
`SheafOfModules.DifferentialGradedModule.freeHomotopy_delta` asks for. -/
noncomputable def boundaryPairImageFamily (τ : P ⟶ M) :
    GradedGeneratorFamily (boundaryPairs τ.toHomologicalComplex)
      (GradedModule.ofDifferentialGraded M) :=
  (boundaryPairFamily τ).map (GradedModule.ofDifferentialGradedMap τ)

/-- **The null-homotopy of the inductive step**: the lift of the family of primitives to the free
graded module on the boundary pairs, read in degree `n + 1` and transported from `M^{(n+1)-1}` to
`M^n`. This is `SheafOfModules.DifferentialGradedModule.freeHomotopy` at the family of
primitives. -/
noncomputable def stepHomotopy (τ : P ⟶ M) (n : ℤ) :
    (freeDGModule (boundaryPairs τ.toHomologicalComplex) A).complex.X (n + 1) ⟶ M.complex.X n :=
  freeHomotopy (boundaryPairs τ.toHomologicalComplex) A M (primitiveFamily τ) n

/-- **The homotopy sends the generator named by a boundary pair of degree `n + 1` to the second
component of that pair.** -/
theorem stepHomotopy_generator (τ : P ⟶ M) (n : ℤ) (V : Cᵒᵖ)
    (y : (boundaryPairObj τ.toHomologicalComplex (n + 1)).val.obj V) :
    homSections (stepHomotopy τ n) V
        (freeGeneratorSection A.toGradedAlgebra (boundaryPairs τ.toHomologicalComplex)
          (n + 1) V (boundaryPairSection τ.toHomologicalComplex (n + 1) V y)
          (boundaryPairSection_hasDegree τ.toHomologicalComplex (n + 1) V y)) =
      castHom M.complex.X (degSuccSubOne n) V
        (homSections (boundaryPairPrimitive τ.toHomologicalComplex (n + 1)) V y) :=
  (freeHomotopy_generator (boundaryPairs τ.toHomologicalComplex) A M (primitiveFamily τ) n V _
      (boundaryPairSection_hasDegree τ.toHomologicalComplex (n + 1) V y)).trans
    (congrArg (fun z => castHom M.complex.X (degSuccSubOne n) V
        (homSections (boundaryPairPrimitive τ.toHomologicalComplex (n + 1)) V z))
      (boundaryPairSection_pair_self τ.toHomologicalComplex (n + 1) V y))

/-- **The homotopy is right `A`-linear**, in the degree-shifted form a map out of a cone
consumes: the degree `(n + 1) + i` of a product is the degree `(n + i) + 1` at which the homotopy
reads it. -/
theorem stepHomotopy_mul (τ : P ⟶ M) (n i : ℤ) (U : Cᵒᵖ)
    (x : ((freeDGModule (boundaryPairs τ.toHomologicalComplex) A).complex.X (n + 1)).val.obj U)
    (y : (A.complex.X i).val.obj U) :
    (stepHomotopy τ (n + i)).val.app U
        (gradedCast
          (fun q ↦ ((freeDGModule (boundaryPairs τ.toHomologicalComplex) A).complex.X q).val.obj U)
          (show (n + 1) + i = (n + i) + 1 by omega)
          (((freeDGModule (boundaryPairs τ.toHomologicalComplex) A).mul (n + 1) i).app U x y)) =
      (M.mul n i).app U ((stepHomotopy τ n).val.app U x) y :=
  freeHomotopy_mul (boundaryPairs τ.toHomologicalComplex) A M (primitiveFamily τ) n i U x y

/-- **The graded homomorphism underlying `A[S] ⟶ P ⟶ M` is the lift of the family of images of
the boundary pairs**, which is what identifies the right-hand side of the general null-homotopy
identity with the composite the cone needs. -/
theorem liftHom_boundaryPairImageFamily (τ : P ⟶ M) :
    GradedModule.Hom.comp
        (liftHom A.toGradedAlgebra (boundaryPairs τ.toHomologicalComplex)
          (GradedModule.ofDifferentialGraded P) (boundaryPairFamily τ))
        (GradedModule.ofDifferentialGradedMap τ) =
      liftHom A.toGradedAlgebra (boundaryPairs τ.toHomologicalComplex)
        (GradedModule.ofDifferentialGraded M) (boundaryPairImageFamily τ) :=
  liftHom_comp A.toGradedAlgebra (boundaryPairs τ.toHomologicalComplex) (boundaryPairFamily τ)
    (GradedModule.ofDifferentialGradedMap τ)

/-- **The homotopy is a null-homotopy of the composite `A[S] ⟶ P ⟶ M`.** -/
theorem stepHomotopy_delta (τ : P ⟶ M) (n : ℤ) :
    stepHomotopy τ n ≫ M.complex.d n (n + 1)
        + (freeDGModule (boundaryPairs τ.toHomologicalComplex) A).complex.d (n + 1) ((n + 1) + 1) ≫
          stepHomotopy τ (n + 1)
      = (dgLiftHom (boundaryPairs τ.toHomologicalComplex) A P (boundaryPairFamily τ)
          (boundaryPairFamily_closed τ) ≫ τ).toHomologicalComplex.f (n + 1) :=
  (freeHomotopy_delta (boundaryPairs τ.toHomologicalComplex) A M (primitiveFamily τ)
      (boundaryPairImageFamily τ) (fun j V s hs => d_boundaryPairPrimitive τ j V s hs) n).trans
    (congrArg (fun φ : GradedModule.Hom
        (freeGradedModule A.toGradedAlgebra (boundaryPairs τ.toHomologicalComplex))
        (GradedModule.ofDifferentialGraded M) => φ.app (n + 1))
      (liftHom_boundaryPairImageFamily τ)).symm

/-! ### The map from the next stage of the tower -/

/-- **The map to `M` from the next stage of the tower of the first proof of Tag 0FSH**: on `P` it
is `τ`, and it sends the generator named by a boundary pair to the second component of that pair.
The twisted extension is the cone of `A[S] ⟶ P`, so this is the homomorphism out of a cone
determined by `τ` together with the null-homotopy
`SheafOfModules.DifferentialGradedModule.stepHomotopy`. -/
noncomputable def towerStepMap (τ : P ⟶ M) :
    twistedExtension (boundaryPairs τ.toHomologicalComplex) P (boundaryPairFamily τ)
      (boundaryPairFamily_closed τ) ⟶ M :=
  (conePackage (dgLiftHom (boundaryPairs τ.toHomologicalComplex) A P (boundaryPairFamily τ)
      (boundaryPairFamily_closed τ))).desc τ (stepHomotopy τ) (stepHomotopy_mul τ)
    (stepHomotopy_delta τ)

/-- **The map from the next stage of the tower restricts to `τ` on `P`.** -/
theorem twistedExtensionInclusion_towerStepMap (τ : P ⟶ M) :
    twistedExtensionInclusion (boundaryPairs τ.toHomologicalComplex) P (boundaryPairFamily τ)
        (boundaryPairFamily_closed τ) ≫ towerStepMap τ = τ :=
  (conePackage (dgLiftHom (boundaryPairs τ.toHomologicalComplex) A P (boundaryPairFamily τ)
      (boundaryPairFamily_closed τ))).inclusion_desc τ (stepHomotopy τ) (stepHomotopy_mul τ)
    (stepHomotopy_delta τ)

end SheafOfModules.DifferentialGradedModule

end
