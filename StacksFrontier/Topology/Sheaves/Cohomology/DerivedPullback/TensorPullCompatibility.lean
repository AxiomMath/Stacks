module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorIsoAlongAComposite
import StacksCore.Tactic.StacksAttribute

/-!
# Compatibility of the pullback-tensor comparison with the ordinary total tensor complex

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces and let `K` and `M` be complexes
of `𝒪_Y`-modules.  **Stacks 0FP0** asserts that the diagram

```
Lf^*(K ⊗^L_{𝒪_Y} M)  ⟶  Lf^*Tot(K ⊗_{𝒪_Y} M)
        |                           |
        v                           v
Lf^*K ⊗^L_{𝒪_X} Lf^*M        f^*Tot(K ⊗_{𝒪_Y} M)
        |                           |
        v                           v
 f^*K ⊗^L_{𝒪_X} f^*M    ⟶   Tot(f^*K ⊗_{𝒪_X} f^*M)
```

commutes.  The two horizontal arrows are the canonical map from the derived tensor product to
the ordinary total tensor complex (Stacks 06YU), on `Y` and on `X`; the upper left vertical
arrow is Stacks 079U; the two right hand vertical arrows are the comparison
`Lf^*(QN) ⟶ Q(f^*N)` and the comparison of total complexes of Stacks 01CD; and the lower left
vertical arrow is `Lf^*(QN) ⟶ Q(f^*N)` in each tensor factor.

## Main results

* `derivedPullbackTensorIso_hom_app_comp_rightComparison_of_complexes`, in this namespace:
  for *arbitrary* complexes `K, M` of `𝒪_Y`-modules, the comparison of Stacks 079U followed by
  `Stacks.Cohomology.DerivedPullbackTensor.rightComparison` is
  `Stacks.Cohomology.DerivedPullbackTensor.leftComparison`.
* `Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso_toTensor_comm`:
  **Stacks 0FP0**, the diagram above, written out arrow by arrow.

## The argument

`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso_hom_app_comp_rightComparison`
is this identity at a pair of K-flat complexes, where it holds because that is how Stacks 079U
is *constructed*: there both `Lf^*(K ⊗^L_{𝒪_Y} M)` and `Lf^*K ⊗^L_{𝒪_X} Lf^*M` are computed by
ordinary total tensor complexes, and the comparison between them is the composite of the two
invertible comparisons into `Q(f^*Tot(K ⊗_{𝒪_Y} M))`.

The source's proof of 0FP0 passes from there to arbitrary complexes by choosing K-flat
resolutions `P ⟶ K` and `Q ⟶ M`, noting that the three rows of the diagram are natural in the
pair, and observing that "the left hand side of the diagram is the left hand side of the
diagram" — that is, that the resolved diagram already commutes.  That is exactly the shape of
the proof below: both sides of the identity are components of natural transformations out of
`(K, M) ↦ Lf^*(QK ⊗^L_{𝒪_Y} QM)`, this functor carries the pair of resolutions to an
isomorphism (the derived pullback of the derived tensor product of two isomorphisms of the
derived category), and an equality of components transports along an epimorphism in the source.
No boundedness, flatness or quasi-coherence hypothesis enters, and no hypothesis survives into
the statement.

## Implementation notes

*Why the descent is by resolutions and not by the localization.*
`Stacks.Cohomology.DerivedPullbackTensor.natTrans_ext_of_kFlat` descends an identity of
transformations between functors on `D(𝒪_Y) × D(𝒪_Y)`.  It does not apply here: the common
target of the two transformations is
`Tot(- ⊗_{𝒪_Y} -) ⋙ f^* ⋙ Q`, a functor on *pairs of complexes* which does not factor through
`D(𝒪_Y) × D(𝒪_Y)` at all — the whole content of the diagram is a statement about the chosen
representatives.  What descends is therefore not the identity but the equality of two
components, and the instrument for that is a single resolution of the pair, which is what the
source uses.

*The statement is phrased against the two comparisons first.*  The implementation notes of
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorIsoAlongAComposite`
record that every mention of
`Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair` or of
`Stacks.Cohomology.DerivedPullbackTensor.pullbackTensorComplexNatIso` costs some twenty
thousand heartbeats in instance synthesis alone, and that a chase phrased against
`Stacks.Cohomology.DerivedPullbackTensor.leftComparison` and
`Stacks.Cohomology.DerivedPullbackTensor.rightComparison` throughout is cheap by comparison.
The resolution argument is therefore carried out at that spelling, and the arrow-by-arrow form
of the diagram — which does mention both expensive terms — is obtained from it by one
cancellation, in its own declaration.

## References

* [Stacks Project, Tag 0FP0](https://stacks.math.columbia.edu/tag/0FP0)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 079R](https://stacks.math.columbia.edu/tag/079R)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped CategoryTheory.Prod

namespace Stacks.Cohomology.DerivedPullbackTensor

universe u

/-- **The descent step of the source's proof, as pure arrow algebra.**  Given three
commutative squares with a common left edge `m`, a common right edge `k` and matching middle
edge `n`, a triangle `a ≫ b = c` on the left transports to the triangle `a' ≫ b' = c'` on the
right as soon as `m` is an epimorphism.

In the application `m` is the image of a pair of K-flat resolutions under
`(K, M) ↦ Lf^*(QK ⊗^L_{𝒪_Y} QM)` and the three squares are naturality of the three
transformations in the diagram.  Every arrow is implicit, so each is fixed by the square it
occurs in rather than re-elaborated from a spelling written out here: the term
`(Q.prod Q ⋙ pullbackOfTensor f).map (p ×ₘ q)`, written on its own, leaves a universe
constraint unsolved. -/
private lemma eq_of_epi_squares {C : Type*} [Category C] {V V' W W' Z Z' : C}
    {m : V ⟶ V'} {n : W ⟶ W'} {k : Z ⟶ Z'}
    {a : V ⟶ W} {a' : V' ⟶ W'} {b : W ⟶ Z} {b' : W' ⟶ Z'} {c : V ⟶ Z} {c' : V' ⟶ Z'}
    (ha : m ≫ a' = a ≫ n) (hb : n ≫ b' = b ≫ k) (hc : m ≫ c' = c ≫ k) (hm : Epi m)
    (h : a ≫ b = c) : a' ≫ b' = c' := by
  have := hm
  apply (cancel_epi m).1
  rw [← Category.assoc, ha, Category.assoc, hb, ← Category.assoc, h, hc]

attribute [local instance] HasDerivedCategory.standard

attribute [local implicit_reducible] structureSheafRing
  StacksDraft.KFlat.modulePullback

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]


/-- **Stacks 079U against the right comparison, at arbitrary complexes.**  For *any* complexes
`K, M` of `𝒪_Y`-modules the comparison

`Lf^*(QK ⊗^L_{𝒪_Y} QM) ≅ Lf^*(QK) ⊗^L_{𝒪_X} Lf^*(QM)`

followed by `Stacks.Cohomology.DerivedPullbackTensor.rightComparison` is
`Stacks.Cohomology.DerivedPullbackTensor.leftComparison`.

`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso_hom_app_comp_rightComparison`
is this at a pair of K-flat complexes.  Both sides are components of natural transformations
out of `(K, M) ↦ Lf^*(QK ⊗^L_{𝒪_Y} QM)`; a pair of K-flat resolutions `P ⟶ K`, `Q ⟶ M`
(Stacks 06YS) is carried by that functor to an isomorphism, since each resolution becomes
invertible in `D(𝒪_Y)`, and an equality of components transports along it. -/
theorem derivedPullbackTensorIso_hom_app_comp_rightComparison_of_complexes
    (K L : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :
    (derivedPullbackTensorIso f).hom.app
          (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) ≫
        (rightComparison f).app (K, L) =
      (leftComparison f).app (K, L) := by
  obtain ⟨P, p, hP, -, hp, -⟩ :=
    AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.exists_kFlatResolution Y K
  obtain ⟨M, q, hM, -, hq, -⟩ :=
    AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.exists_kFlatResolution Y L
  have hpair : IsIso (DerivedCategory.Q.map p ×ₘ DerivedCategory.Q.map q) :=
    (isIso_prod_iff _ _).2
      ⟨(DerivedCategory.isIso_Q_map_iff_quasiIso _ p).2 hp,
        (DerivedCategory.isIso_Q_map_iff_quasiIso _ q).2 hq⟩
  have hepi : Epi ((pullbackOfTensor f).map
      (DerivedCategory.Q.map p ×ₘ DerivedCategory.Q.map q)) :=
    inferInstance
  refine eq_of_epi_squares
    ((Functor.whiskerLeft (DerivedCategory.Q.prod DerivedCategory.Q)
      (derivedPullbackTensorIso f).hom).naturality (p ×ₘ q))
    ((rightComparison f).naturality (p ×ₘ q))
    ((leftComparison f).naturality (p ×ₘ q)) hepi
    (derivedPullbackTensorIso_hom_app_comp_rightComparison f P M hP hM)

/-- **Stacks 0FP0.**  Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces and let
`K, M` be complexes of `𝒪_Y`-modules.  The diagram

```
Lf^*(K ⊗^L_{𝒪_Y} M)  ⟶  Lf^*Tot(K ⊗_{𝒪_Y} M)
        |                           |
        v                           v
Lf^*K ⊗^L_{𝒪_X} Lf^*M        f^*Tot(K ⊗_{𝒪_Y} M)
        |                           |
        v                           v
 f^*K ⊗^L_{𝒪_X} f^*M    ⟶   Tot(f^*K ⊗_{𝒪_X} f^*M)
```

commutes: the left hand column — Stacks 079U, then the comparison `Lf^*(QN) ⟶ Q(f^*N)` in each
tensor factor — followed by the canonical map to the ordinary total tensor complex on `X`
equals the top row — the derived pullback of the canonical map to the ordinary total tensor
complex on `Y` — followed by the right hand column, the comparison `Lf^*(QN) ⟶ Q(f^*N)` at
`Tot(K ⊗_{𝒪_Y} M)` and then the comparison of total complexes of Stacks 01CD.

This is
`derivedPullbackTensorIso_hom_app_comp_rightComparison_of_complexes` with the right comparison
written out: postcomposing with the comparison of total complexes cancels the inverse that the
right comparison ends with, leaving the six arrows of the source's diagram. -/
@[stacks 0FP0]
theorem derivedPullbackTensorIso_toTensor_comm
    (K L : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :
    (derivedPullbackTensorIso f).hom.app
          (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) ≫
        (Functor.uncurry.obj
              (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf)).map
            ((derivedPullbackNatTrans f).app K ×ₘ (derivedPullbackNatTrans f).app L) ≫
          (derivedToTensorNatTrans X).app
            ((pullbackComplex f).obj K, (pullbackComplex f).obj L) =
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).map
          ((derivedToTensorNatTrans Y).app (K, L)) ≫
        (derivedPullbackNatTrans f).app
            ((totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf)).obj (K, L)) ≫
          DerivedCategory.Q.map ((pullbackTensorComplexNatIso f).hom.app (K, L)) := by
  have hih : DerivedCategory.Q.map ((pullbackTensorComplexNatIso f).inv.app (K, L)) ≫
      DerivedCategory.Q.map ((pullbackTensorComplexNatIso f).hom.app (K, L)) = 𝟙 _ :=
    (DerivedCategory.Q.mapIso ((pullbackTensorComplexNatIso f).app (K, L))).inv_hom_id
  have hkey : (derivedPullbackTensorIso f).hom.app
          (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) ≫
        (Functor.uncurry.obj
              (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf)).map
            ((derivedPullbackNatTrans f).app K ×ₘ (derivedPullbackNatTrans f).app L) ≫
          (derivedToTensorNatTrans X).app
              ((pullbackComplex f).obj K, (pullbackComplex f).obj L) ≫
            DerivedCategory.Q.map ((pullbackTensorComplexNatIso f).inv.app (K, L)) =
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).map
          ((derivedToTensorNatTrans Y).app (K, L)) ≫
        (derivedPullbackNatTrans f).app
          ((totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf)).obj (K, L)) :=
    derivedPullbackTensorIso_hom_app_comp_rightComparison_of_complexes f K L
  exact comp_eq_of_comp_inv _ _ _ _ _ _ _ hih hkey

end Stacks.Cohomology.DerivedPullbackTensor

end

