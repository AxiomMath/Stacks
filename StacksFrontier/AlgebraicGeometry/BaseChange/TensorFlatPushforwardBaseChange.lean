module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.TensorAndSheafHomBaseChange
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.BaseChangeMap
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorComparison
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
public import StacksFrontier.Algebra.Homology.HomotopyCategory.Minus
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import StacksCore.Tactic.StacksAttribute

/-!
# Base change for the derived pushforward of a derived tensor product with a relatively flat
complex

Let

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

be a cartesian diagram of schemes with `f` quasi-compact and quasi-separated, let `E` be an
object of `D_QCoh(𝒪_X)` and let `𝒢^•` be a bounded-above complex of quasi-coherent
`𝒪_X`-modules which are flat over `S`. Stacks 0A1D says that the formation of
`Rf_*(E ⊗^L_{𝒪_X} 𝒢^•)` commutes with arbitrary base change; the precise statement, which the
source defers to its proof, is that the canonical map

`Lg^*Rf_*(E ⊗^L_{𝒪_X} 𝒢^•) ⟶ Rf'_*(L(g')^*E ⊗^L_{𝒪_{X'}} (g')^*𝒢^•)`

is an isomorphism. **The right-hand side uses the ordinary pullback `(g')^*𝒢^•`**, not the
derived one; the source sets that in bold, and this module keeps it: the second factor of the
comparison is built from the derived-to-ordinary comparison
`L(g')^*𝒢^• ⟶ (g')^*𝒢^•`, which is not assumed invertible anywhere below.

## Main definitions

* `AlgebraicGeometry.PointwiseBaseChangeIsIso`: condition (1) of Stacks 0DJ8 for a datum
  `(K, K', φ)`, as a named predicate — the invertibility of the pointwise base-change map of
  Stacks 0DJ7 at every point of `X'` and in every degree.
* `AlgebraicGeometry.tensorFlatBaseChangeMap`: the canonical map of Stacks 0A1D displayed
  above, constructed as the derived base-change map of Stacks 08HY followed by `Rf'_*` of the
  base-change comparison for a derived tensor product.
* `AlgebraicGeometry.GlobalBaseChangeIsIsoOfPointwise`,
  `AlgebraicGeometry.PointwiseBaseChangeTensor`,
  `AlgebraicGeometry.PointwiseBaseChangeOfFlatOver`: the conclusion of Stacks 0DJ9, conclusion
  (1) of Stacks 0DJA and the stalk check of the proof of Stacks 0A1D, each as a Prop quantified
  over all cartesian squares. They are proved in
  `StacksFrontier.AlgebraicGeometry.BaseChange.TensorFlatPushforwardBaseChangeCartesian`.

## Main results

* `AlgebraicGeometry.pointwiseBaseChangeIsIso_tensor_of_isIso`: the step of Stacks 0DJA (1)
  for an invertible `φ`, over an arbitrary commutative square.
* `AlgebraicGeometry.isIso_tensorFlatBaseChangeMap_of_kFlat`: the conclusion for a K-flat
  `𝒢^•`, from Stacks 0DJ9 alone. This is *not* Stacks 0A1D — K-flatness over `𝒪_X` is neither
  implied by nor implies flatness of the terms over `S`.

Stacks 0A1D itself is `AlgebraicGeometry.isIso_tensorFlatBaseChangeMap_of_isPullback`.

## Implementation notes

*Which of the three conditions of Stacks 0DJ8.* The three Props below read the equivalent
conditions of Stacks 0DJ8 in form (1), the pointwise condition: it is the form the stalk check of
the proof of Stacks 0A1D produces, and it is available at the standard model of the derived
category, which is the model the base-change map of Stacks 08HY is carried at.

## References

* [Stacks Project, Tag 0A1D](https://stacks.math.columbia.edu/tag/0A1D)
* [Stacks Project, Tag 0DJ7](https://stacks.math.columbia.edu/tag/0DJ7)
* [Stacks Project, Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8)
* [Stacks Project, Tag 0DJ9](https://stacks.math.columbia.edu/tag/0DJ9)
* [Stacks Project, Tag 0DJA](https://stacks.math.columbia.edu/tag/0DJA)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 08DW](https://stacks.math.columbia.edu/tag/08DW)
* [Stacks Project, Tag 08DX](https://stacks.math.columbia.edu/tag/08DX)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 08KT](https://stacks.math.columbia.edu/tag/08KT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward)
open Stacks.Cohomology.DerivedBaseChange (derivedBaseChangeMap)
open Stacks.Cohomology.DerivedBaseChangeComparison (baseChangeTensorComparison)
open Stacks.Cohomology.DerivedPullbackTensor (derivedPullbackNatTrans pullbackComplex)
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor)

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

attribute [local implicit_reducible] structureSheafRing
  StacksDraft.KFlat.modulePullback

/-! ### Condition (1) of Stacks 0DJ8, as a predicate -/

/-- **Condition (1) of Stacks 0DJ8.** For a commutative square of schemes, `K` in `D(𝒪_X)`,
`K'` in `D(𝒪_{X'})` and `φ : L(g')^*K ⟶ K'`, the pointwise base-change map of Stacks 0DJ7 is
invertible at every point of `X'` and in every degree.

The source asserts this to be equivalent to its conditions (2) and (3), which quantify over
Cartesian affine-open charts; that equivalence is not carried by this library, so the three
conclusions below that say "the equivalent conditions of Stacks 0DJ8 hold" are all read in this
form. -/
public def PointwiseBaseChangeIsIso {X X' S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (f' : X' ⟶ S') (g' : X' ⟶ X) (w : g' ≫ f = f' ≫ g)
    (K : DerivedCategory X.Modules) (K' : DerivedCategory X'.Modules)
    (φ : (derivedPullback g'.toLRSHom.toShHom).obj K ⟶ K') : Prop :=
  ∀ (x' : X') (n : ℤ), IsIso (baseChangeCohomologyMap f g f' g' w K K' φ x' n)

/-! ### The canonical map of Stacks 0A1D -/

/-- **The canonical map of Stacks 0A1D**, as the precise statement in the source's proof
displays it:

`Lg^*Rf_*(E ⊗^L_{𝒪_X} 𝒢^•) ⟶ Rf'_*(L(g')^*E ⊗^L_{𝒪_{X'}} (g')^*𝒢^•)`.

It is the derived base-change map of Stacks 08HY at `E ⊗^L_{𝒪_X} 𝒢^•`, followed by `Rf'_*` of
the base-change comparison for a derived tensor product of Stacks 0DJA, taken at the
derived-to-ordinary comparison `L(g')^*𝒢^• ⟶ (g')^*𝒢^•`.

On the right-hand side the complex `𝒢^•` is pulled back by the **ordinary** functor `(g')^*`,
which is what the source's boldface insists on; the derived-to-ordinary comparison that makes
this possible is the `φ` of the second factor, and it is never assumed invertible. -/
@[stacks 0A1D "the canonical map whose invertibility is the tag's conclusion, as the precise \
statement in the proof displays it: the derived base-change map of Stacks 08HY at E ⊗^L 𝒢^•, \
followed by Rf'_* of the base-change comparison of Stacks 0DJA taken at the derived-to-ordinary \
comparison L(g')^*𝒢^• ⟶ (g')^*𝒢^•. The target uses the ORDINARY pullback (g')^*𝒢^•, which the \
source sets in bold, and the derived-to-ordinary comparison is not assumed invertible"]
public def tensorFlatBaseChangeMap {X X' S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (f' : X' ⟶ S') (g' : X' ⟶ X)
    (sq : g'.toLRSHom.toShHom ≫ f.toLRSHom.toShHom =
      f'.toLRSHom.toShHom ≫ g.toLRSHom.toShHom)
    (E : DerivedCategory X.Modules) (G : CochainComplex X.Modules ℤ) :
    (derivedPullback g.toLRSHom.toShHom).obj
        ((derivedPushforward f.toLRSHom.toShHom).obj
          (((derivedTensorProductFunctor X.sheaf).obj E).obj (DerivedCategory.Q.obj G))) ⟶
      (derivedPushforward f'.toLRSHom.toShHom).obj
        (((derivedTensorProductFunctor X'.sheaf).obj
            ((derivedPullback g'.toLRSHom.toShHom).obj E)).obj
          (DerivedCategory.Q.obj ((pullbackComplex g'.toLRSHom.toShHom).obj G))) :=
  derivedBaseChangeMap g'.toLRSHom.toShHom f'.toLRSHom.toShHom f.toLRSHom.toShHom
      g.toLRSHom.toShHom sq
      (((derivedTensorProductFunctor X.sheaf).obj E).obj (DerivedCategory.Q.obj G)) ≫
    (derivedPushforward f'.toLRSHom.toShHom).map
      (baseChangeTensorComparison g'.toLRSHom.toShHom E (DerivedCategory.Q.obj G)
        (DerivedCategory.Q.obj ((pullbackComplex g'.toLRSHom.toShHom).obj G))
        ((derivedPullbackNatTrans g'.toLRSHom.toShHom).app G))

/-! ### The three steps of the source proof of Stacks 0A1D, as Props -/

/-- **The conclusion of Stacks 0DJ9**, with the equivalent conditions of Stacks 0DJ8 read in
form (1): for a cartesian square of schemes with `f` quasi-compact and quasi-separated, a
`K` in `D_QCoh(𝒪_X)`, a `K'` in `D_QCoh(𝒪_{X'})` and a `φ : L(g')^*K ⟶ K'` satisfying the
pointwise condition, the composition `Lg^*Rf_*K ⟶ Rf'_*L(g')^*K ⟶ Rf'_*K'` is an isomorphism.

It is proved as `AlgebraicGeometry.globalBaseChangeIsIsoOfPointwise`. -/
public def GlobalBaseChangeIsIsoOfPointwise : Prop :=
  ∀ {X X' S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X),
    IsPullback g' f' f g → QuasiCompact f → QuasiSeparated f →
    ∀ (w : g' ≫ f = f' ≫ g)
      (sq : g'.toLRSHom.toShHom ≫ f.toLRSHom.toShHom =
        f'.toLRSHom.toShHom ≫ g.toLRSHom.toShHom)
      (K : DerivedCategory X.Modules) (K' : DerivedCategory X'.Modules)
      (φ : (derivedPullback g'.toLRSHom.toShHom).obj K ⟶ K'),
      (∀ n : ℤ, ((DerivedCategory.homologyFunctor X.Modules n).obj K).IsQuasicoherent) →
      (∀ n : ℤ, ((DerivedCategory.homologyFunctor X'.Modules n).obj K').IsQuasicoherent) →
      PointwiseBaseChangeIsIso f g f' g' w K K' φ →
      IsIso (derivedBaseChangeMap g'.toLRSHom.toShHom f'.toLRSHom.toShHom
          f.toLRSHom.toShHom g.toLRSHom.toShHom sq K ≫
        (derivedPushforward f'.toLRSHom.toShHom).map φ)

/-- **Conclusion (1) of Stacks 0DJA**, with the equivalent conditions of Stacks 0DJ8 read in
form (1): for a cartesian square of schemes, if the pointwise condition holds for `(K, K', φ)` then
it holds for `L(g')^*(E ⊗^L_{𝒪_X} K) ⟶ L(g')^*E ⊗^L_{𝒪_{X'}} K'`, for every `E`.

It is proved as `AlgebraicGeometry.pointwiseBaseChangeTensor`. -/
public def PointwiseBaseChangeTensor : Prop :=
  ∀ {X X' S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X),
    IsPullback g' f' f g →
    ∀ (w : g' ≫ f = f' ≫ g) (E K : DerivedCategory X.Modules)
      (K' : DerivedCategory X'.Modules)
      (φ : (derivedPullback g'.toLRSHom.toShHom).obj K ⟶ K'),
      PointwiseBaseChangeIsIso f g f' g' w K K' φ →
      PointwiseBaseChangeIsIso f g f' g' w
        (((derivedTensorProductFunctor X.sheaf).obj E).obj K)
        (((derivedTensorProductFunctor X'.sheaf).obj
          ((derivedPullback g'.toLRSHom.toShHom).obj E)).obj K')
        (baseChangeTensorComparison g'.toLRSHom.toShHom E K K' φ)

/-- **The stalk check in the proof of Stacks 0A1D.** For a cartesian square of schemes and a
bounded-above complex `𝒢^•` of quasi-coherent `𝒪_X`-modules whose terms are flat over `S`, the
pointwise condition of Stacks 0DJ8 holds for the derived-to-ordinary comparison
`L(g')^*𝒢^• ⟶ (g')^*𝒢^•`.

This is the one step the source performs rather than cites: it checks the condition on stalks,
where `𝒢^•_x ⊗_{𝒪_{S,s}} 𝒪_{S',s'}` computes the derived tensor product because the terms of
`𝒢^•` are flat over `S`. It is proved as `AlgebraicGeometry.pointwiseBaseChangeOfFlatOver`. -/
public def PointwiseBaseChangeOfFlatOver : Prop :=
  ∀ {X X' S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X),
    IsPullback g' f' f g →
    ∀ (w : g' ≫ f = f' ≫ g) (G : CochainComplex X.Modules ℤ),
      CochainComplex.minus X.Modules G →
      (∀ n : ℤ, (G.X n).IsQuasicoherent) →
      (∀ n : ℤ, IsFlatOver f.toLRSHom.toShHom (G.X n)) →
      PointwiseBaseChangeIsIso f g f' g' w (DerivedCategory.Q.obj G)
        (DerivedCategory.Q.obj ((pullbackComplex g'.toLRSHom.toShHom).obj G))
        ((derivedPullbackNatTrans g'.toLRSHom.toShHom).app G)

/-! ### The case in which conclusion (1) of Stacks 0DJA is available -/

/-- **Conclusion (1) of Stacks 0DJA for an invertible `φ`.** If `φ : L(g')^*K ⟶ K'` is an
isomorphism and the pointwise condition of Stacks 0DJ8 holds for the monoidality isomorphism of
Stacks 079U at `(E, K)`, then it holds for the base-change comparison
`L(g')^*(E ⊗^L_{𝒪_X} K) ⟶ L(g')^*E ⊗^L_{𝒪_{X'}} K'`.

This is `AlgebraicGeometry.isIso_baseChangeCohomologyMap_baseChangeTensorComparison` read
through `PointwiseBaseChangeIsIso`. It is not conclusion (1) of Stacks 0DJA, whose hypothesis
is the pointwise condition for `(K, K', φ)` itself and whose `φ` is arbitrary. -/
public theorem pointwiseBaseChangeIsIso_tensor_of_isIso {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X) (w : g' ≫ f = f' ≫ g)
    (E K : DerivedCategory X.Modules) (K' : DerivedCategory X'.Modules)
    (φ : (derivedPullback g'.toLRSHom.toShHom).obj K ⟶ K') (hφ : IsIso φ)
    (hEK : PointwiseBaseChangeIsIso f g f' g' w
      (((derivedTensorProductFunctor X.sheaf).obj E).obj K)
      (((derivedTensorProductFunctor X'.sheaf).obj
        ((derivedPullback g'.toLRSHom.toShHom).obj E)).obj
        ((derivedPullback g'.toLRSHom.toShHom).obj K))
      ((Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso
        g'.toLRSHom.toShHom).hom.app (E, K))) :
    PointwiseBaseChangeIsIso f g f' g' w
      (((derivedTensorProductFunctor X.sheaf).obj E).obj K)
      (((derivedTensorProductFunctor X'.sheaf).obj
        ((derivedPullback g'.toLRSHom.toShHom).obj E)).obj K')
      (baseChangeTensorComparison g'.toLRSHom.toShHom E K K' φ) :=
  isIso_baseChangeCohomologyMap_baseChangeTensorComparison f g f' g' w E K K' φ hφ hEK

/-- **The map of Stacks 0A1D for a K-flat `𝒢^•`.** If `𝒢^•` is K-flat as a complex of
`𝒪_X`-modules then the derived-to-ordinary comparison `L(g')^*𝒢^• ⟶ (g')^*𝒢^•` is invertible, so
`pointwiseBaseChangeIsIso_tensor_of_isIso` applies: what is left is the pointwise condition at the
monoidality isomorphism of Stacks 079U, which is the hypothesis `hEG`, and Stacks 0DJ9.

This is **not** Stacks 0A1D. K-flatness over `𝒪_X` neither implies nor is implied by flatness
of the terms over `S`, so this is a statement about a different class of complexes. -/
public theorem isIso_tensorFlatBaseChangeMap_of_kFlat
    (h0DJ9 : GlobalBaseChangeIsIsoOfPointwise.{u})
    {X X' S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
    (hsq : IsPullback g' f' f g) (hqc : QuasiCompact f) (hqs : QuasiSeparated f)
    (w : g' ≫ f = f' ≫ g)
    (sq : g'.toLRSHom.toShHom ≫ f.toLRSHom.toShHom =
      f'.toLRSHom.toShHom ≫ g.toLRSHom.toShHom)
    (E : DerivedCategory X.Modules) (G : CochainComplex X.Modules ℤ)
    (hGkflat : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat X.toRingedSpace G)
    (hEG : PointwiseBaseChangeIsIso f g f' g' w
      (((derivedTensorProductFunctor X.sheaf).obj E).obj (DerivedCategory.Q.obj G))
      (((derivedTensorProductFunctor X'.sheaf).obj
        ((derivedPullback g'.toLRSHom.toShHom).obj E)).obj
        ((derivedPullback g'.toLRSHom.toShHom).obj (DerivedCategory.Q.obj G)))
      ((Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso
        g'.toLRSHom.toShHom).hom.app (E, DerivedCategory.Q.obj G)))
    (hK : ∀ n : ℤ, ((DerivedCategory.homologyFunctor X.Modules n).obj
      (((derivedTensorProductFunctor X.sheaf).obj E).obj
        (DerivedCategory.Q.obj G))).IsQuasicoherent)
    (hK' : ∀ n : ℤ, ((DerivedCategory.homologyFunctor X'.Modules n).obj
      (((derivedTensorProductFunctor X'.sheaf).obj
          ((derivedPullback g'.toLRSHom.toShHom).obj E)).obj
        (DerivedCategory.Q.obj
          ((pullbackComplex g'.toLRSHom.toShHom).obj G)))).IsQuasicoherent) :
    IsIso (tensorFlatBaseChangeMap f g f' g' sq E G) :=
  h0DJ9 f g f' g' hsq hqc hqs w sq _ _ _ hK hK'
    (pointwiseBaseChangeIsIso_tensor_of_isIso f g f' g' w E (DerivedCategory.Q.obj G) _ _
      (Stacks.Cohomology.DerivedPullbackTensor.isIso_derivedPullbackNatTrans_app
        g'.toLRSHom.toShHom G hGkflat)
      hEG)

end AlgebraicGeometry

end
