module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TensorFlatPushforwardBaseChange
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.SheafLevel
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Defs
public import StacksCore.Tactic.StacksAttribute
import StacksFrontier.AlgebraicGeometry.BaseChange.TensorFlatPushforwardBaseChangeCartesian
import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.TensorBaseChange.DerivedSheafHom

/-!
# Base change for the derived pushforward of a derived internal hom into a relatively flat
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
object of `D(𝒪_X)` and let `𝒢^•` be a complex of quasi-coherent `𝒪_X`-modules whose terms are
flat over `S`. Stacks 08IE says that the formation of `Rf_*R𝓗om_{𝒪_X}(E, 𝒢^•)` commutes with
arbitrary base change when `E` is perfect and `𝒢^•` is bounded above, and when `E` is
pseudo-coherent and `𝒢^•` is bounded. The precise statement is that the canonical map

`Lg^*Rf_*R𝓗om_{𝒪_X}(E, 𝒢^•) ⟶ Rf'_*R𝓗om_{𝒪_{X'}}(L(g')^*E, (g')^*𝒢^•)`

is an isomorphism. **The right-hand side uses the ordinary pullback `(g')^*𝒢^•`**, not the
derived one; the source sets that in bold, and this module keeps it: the second factor of the
comparison is built from the derived-to-ordinary comparison `L(g')^*𝒢^• ⟶ (g')^*𝒢^•`, which is
not assumed invertible anywhere below.

## Main definitions

* `AlgebraicGeometry.sheafHomFlatBaseChangeMap`: the canonical map of Stacks 08IE displayed
  above, the derived base-change map of Stacks 08HY followed by `Rf'_*` of the base-change
  comparison for a derived internal hom.
* `AlgebraicGeometry.PointwiseBaseChangeSheafHomOfPerfect` and
  `AlgebraicGeometry.PointwiseBaseChangeSheafHomOfPseudoCoherent`: conclusions (2) and (3) of
  Stacks 0DJA, each as a Prop quantified over all commutative squares.

## Main results

* `AlgebraicGeometry.isIso_sheafHomFlatBaseChangeMap_of_perfect`: **Stacks 08IE case (1)**,
  for `E` perfect and `𝒢^•` bounded above.

## Implementation notes

*The three steps.* The source proof reduces to Stacks 0DJ9 and Stacks 0DJA applied to the
derived-to-ordinary comparison `L(g')^*𝒢^• ⟶ (g')^*𝒢^•`, whose pointwise condition "was shown
in the proof of Lemma 0A1D". The first and the third are
`AlgebraicGeometry.globalBaseChangeIsIsoOfPointwise` and
`AlgebraicGeometry.pointwiseBaseChangeOfFlatOver` of
`StacksFrontier/AlgebraicGeometry/BaseChange/TensorFlatPushforwardBaseChangeCartesian.lean`,
reused verbatim here, and the second is conclusion (2) of Stacks 0DJA,
`AlgebraicGeometry.isIso_baseChangeCohomologyMap_baseChangeSheafHomComparison_of_isPerfect`.

*Which of the three conditions of Stacks 0DJ8.* The equivalent conditions of Stacks 0DJ8 are
used only in form (1), the pointwise condition `AlgebraicGeometry.PointwiseBaseChangeIsIso`.
Forms (2) and (3) quantify over Cartesian affine-open charts and are carried in this library at
the locally small model of `D(𝒪_X)` rather than at `CategoryTheory.HasDerivedCategory.standard`,
which is the model the base-change map of Stacks 08HY is carried at, and no implication between
(1) and them is available; so they cannot appear in the same statement as the map whose
invertibility is asserted here.

*Boundedness below of `K` in Stacks 0DJA (3).* It is read as the existence of a representative
complex vanishing in all degrees below some integer, which is how perfection and
pseudo-coherence are spelled in this library as well, and which the bounded `𝒢^•` of case (2)
supplies by its own strict bound.

*The `D_QCoh` memberships.* Stacks 0DJ9 and Stacks 0DJA each ask their `K` and `K'` to lie in
`D_QCoh`; those hypotheses are kept in the Props below so that neither is stronger than the
result it names. The two of them that Stacks 0DJ9 asks of the two derived internal homs are
hypotheses of the theorem below, `hK` and `hK'`, exactly as
`AlgebraicGeometry.isIso_tensorFlatBaseChangeMap` has them for Stacks 0A1D; the library's form
of Stacks 0DJA (2) asks for neither of the other two.

## References

* [Stacks Project, Tag 08IE](https://stacks.math.columbia.edu/tag/08IE)
* [Stacks Project, Tag 08CB](https://stacks.math.columbia.edu/tag/08CB)
* [Stacks Project, Tag 08CM](https://stacks.math.columbia.edu/tag/08CM)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 08I3](https://stacks.math.columbia.edu/tag/08I3)
* [Stacks Project, Tag 0A1D](https://stacks.math.columbia.edu/tag/0A1D)
* [Stacks Project, Tag 0DJ7](https://stacks.math.columbia.edu/tag/0DJ7)
* [Stacks Project, Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8)
* [Stacks Project, Tag 0DJ9](https://stacks.math.columbia.edu/tag/0DJ9)
* [Stacks Project, Tag 0DJA](https://stacks.math.columbia.edu/tag/0DJA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward)
open Stacks.Cohomology.DerivedBaseChange (derivedBaseChangeMap)
open Stacks.Cohomology.DerivedBaseChangeComparison (baseChangeSheafHomComparison)
open Stacks.Cohomology.DerivedPullbackTensor (derivedPullbackNatTrans pullbackComplex)
open Stacks.SheafOfModules (derivedSheafHom)

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

attribute [local implicit_reducible] structureSheafRing
  StacksDraft.KFlat.modulePullback

/-! ### The canonical map of Stacks 08IE -/

/-- **The canonical map of Stacks 08IE**:

`Lg^*Rf_*R𝓗om_{𝒪_X}(E, 𝒢^•) ⟶ Rf'_*R𝓗om_{𝒪_{X'}}(L(g')^*E, (g')^*𝒢^•)`.

It is the derived base-change map of Stacks 08HY at `R𝓗om_{𝒪_X}(E, 𝒢^•)`, followed by `Rf'_*`
of the base-change comparison for a derived internal hom of Stacks 0DJA, taken at the
derived-to-ordinary comparison `L(g')^*𝒢^• ⟶ (g')^*𝒢^•`.

On the right-hand side the complex `𝒢^•` is pulled back by the **ordinary** functor `(g')^*`,
which is what the source's boldface insists on; the derived-to-ordinary comparison that makes
this possible is the `φ` of the second factor, and it is never assumed invertible. -/
@[stacks 08IE "the canonical map whose invertibility is the tag's conclusion: the derived \
base-change map of Stacks 08HY at R𝓗om(E, 𝒢^•), followed by Rf'_* of the base-change \
comparison of Stacks 0DJA taken at the derived-to-ordinary comparison L(g')^*𝒢^• ⟶ \
(g')^*𝒢^•. The target uses the ORDINARY pullback (g')^*𝒢^•, which the source sets in bold, \
and the derived-to-ordinary comparison is not assumed invertible"]
public def sheafHomFlatBaseChangeMap {X X' S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (f' : X' ⟶ S') (g' : X' ⟶ X)
    (sq : g'.toLRSHom.toShHom ≫ f.toLRSHom.toShHom =
      f'.toLRSHom.toShHom ≫ g.toLRSHom.toShHom)
    (E : DerivedCategory X.Modules) (G : CochainComplex X.Modules ℤ) :
    (derivedPullback g.toLRSHom.toShHom).obj
        ((derivedPushforward f.toLRSHom.toShHom).obj
          (((derivedSheafHom X.sheaf).obj (op E)).obj (DerivedCategory.Q.obj G))) ⟶
      (derivedPushforward f'.toLRSHom.toShHom).obj
        (((derivedSheafHom X'.sheaf).obj
            (op ((derivedPullback g'.toLRSHom.toShHom).obj E))).obj
          (DerivedCategory.Q.obj ((pullbackComplex g'.toLRSHom.toShHom).obj G))) :=
  derivedBaseChangeMap g'.toLRSHom.toShHom f'.toLRSHom.toShHom f.toLRSHom.toShHom
      g.toLRSHom.toShHom sq
      (((derivedSheafHom X.sheaf).obj (op E)).obj (DerivedCategory.Q.obj G)) ≫
    (derivedPushforward f'.toLRSHom.toShHom).map
      (baseChangeSheafHomComparison g'.toLRSHom.toShHom E (DerivedCategory.Q.obj G)
        (DerivedCategory.Q.obj ((pullbackComplex g'.toLRSHom.toShHom).obj G))
        ((derivedPullbackNatTrans g'.toLRSHom.toShHom).app G))

/-! ### Conclusions (2) and (3) of Stacks 0DJA, carried as hypotheses -/

/-- **Conclusion (2) of Stacks 0DJA**, with the equivalent conditions of Stacks 0DJ8 read in
form (1): if the pointwise condition holds for `(K, K', φ)` then it holds for
`L(g')^*R𝓗om_{𝒪_X}(E, K) ⟶ R𝓗om_{𝒪_{X'}}(L(g')^*E, K')`, for every perfect `E` in `D(𝒪_X)`.

The two quasi-coherence hypotheses on `K` and `K'` are the standing hypotheses of Stacks 0DJA,
which asks `K` to lie in `D_QCoh(𝒪_X)` and the map `L(g')^*K ⟶ K'` to be a map of
`D_QCoh(𝒪_{X'})`; nothing beyond perfection is asked of `E`, and no bound of `K`.

The square here is an arbitrary commutative one, which is more than Stacks 0DJA asks: the
library's form of conclusion (2),
`AlgebraicGeometry.isIso_baseChangeCohomologyMap_baseChangeSheafHomComparison_of_isPerfect`, is
for a cartesian square, and that is the form
`AlgebraicGeometry.isIso_sheafHomFlatBaseChangeMap_of_perfect` uses. -/
public def PointwiseBaseChangeSheafHomOfPerfect : Prop :=
  ∀ {X X' S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
    (w : g' ≫ f = f' ≫ g) (E K : DerivedCategory X.Modules)
    (K' : DerivedCategory X'.Modules)
    (φ : (derivedPullback g'.toLRSHom.toShHom).obj K ⟶ K'),
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E →
    (∀ n : ℤ, ((DerivedCategory.homologyFunctor X.Modules n).obj K).IsQuasicoherent) →
    (∀ n : ℤ, ((DerivedCategory.homologyFunctor X'.Modules n).obj K').IsQuasicoherent) →
    PointwiseBaseChangeIsIso f g f' g' w K K' φ →
    PointwiseBaseChangeIsIso f g f' g' w
      (((derivedSheafHom X.sheaf).obj (op E)).obj K)
      (((derivedSheafHom X'.sheaf).obj
        (op ((derivedPullback g'.toLRSHom.toShHom).obj E))).obj K')
      (baseChangeSheafHomComparison g'.toLRSHom.toShHom E K K' φ)

/-- **Conclusion (3) of Stacks 0DJA**, with the equivalent conditions of Stacks 0DJ8 read in
form (1): the same conclusion as (2), for a pseudo-coherent `E` in `D(𝒪_X)` and a `K` bounded
below.

Boundedness below of `K` is read as the existence of a representative complex vanishing in all
degrees below some integer. The two quasi-coherence hypotheses on `K` and `K'` are again the
standing hypotheses of Stacks 0DJA. -/
public def PointwiseBaseChangeSheafHomOfPseudoCoherent : Prop :=
  ∀ {X X' S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
    (w : g' ≫ f = f' ≫ g) (E K : DerivedCategory X.Modules)
    (K' : DerivedCategory X'.Modules)
    (φ : (derivedPullback g'.toLRSHom.toShHom).obj K ⟶ K'),
    RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E →
    (∃ (L : CochainComplex X.Modules ℤ) (a : ℤ), L.IsStrictlyGE a ∧
      Nonempty (DerivedCategory.Q.obj L ≅ K)) →
    (∀ n : ℤ, ((DerivedCategory.homologyFunctor X.Modules n).obj K).IsQuasicoherent) →
    (∀ n : ℤ, ((DerivedCategory.homologyFunctor X'.Modules n).obj K').IsQuasicoherent) →
    PointwiseBaseChangeIsIso f g f' g' w K K' φ →
    PointwiseBaseChangeIsIso f g f' g' w
      (((derivedSheafHom X.sheaf).obj (op E)).obj K)
      (((derivedSheafHom X'.sheaf).obj
        (op ((derivedPullback g'.toLRSHom.toShHom).obj E))).obj K')
      (baseChangeSheafHomComparison g'.toLRSHom.toShHom E K K' φ)

/-! ### Stacks 08IE -/

/-- **Stacks 08IE, case (1).** Let `f : X ⟶ S` be a quasi-compact and quasi-separated morphism
of schemes, let `E` be a perfect object of `D(𝒪_X)` and let `𝒢^•` be a bounded-above complex of
quasi-coherent `𝒪_X`-modules flat over `S`. For every cartesian base-change square the
canonical map

`Lg^*Rf_*R𝓗om_{𝒪_X}(E, 𝒢^•) ⟶ Rf'_*R𝓗om_{𝒪_{X'}}(L(g')^*E, (g')^*𝒢^•)`

of `sheafHomFlatBaseChangeMap` is an isomorphism — note the ordinary pullback of `𝒢^•` on the
right.

The proof is the source's: the flatness of the terms of `𝒢^•` over `S` gives the condition of
Stacks 0DJ8 for `L(g')^*𝒢^• ⟶ (g')^*𝒢^•`
(`AlgebraicGeometry.pointwiseBaseChangeOfFlatOver`), Stacks 0DJA (2)
(`AlgebraicGeometry.isIso_baseChangeCohomologyMap_baseChangeSheafHomComparison_of_isPerfect`)
propagates it to the comparison for `R𝓗om_{𝒪_X}(E, 𝒢^•)`, and Stacks 0DJ9
(`AlgebraicGeometry.globalBaseChangeIsIsoOfPointwise`) turns it into the invertibility of the
displayed map. -/
@[stacks 08IE "case (1) of the tag -- E perfect, 𝒢^• bounded above, each 𝒢^n flat over S -- for \
the canonical map `sheafHomFlatBaseChangeMap`, with the ORDINARY pullback (g')^*𝒢^• on the right \
as the source's boldface demands, the derived-to-ordinary comparison L(g')^*𝒢^• ⟶ (g')^*𝒢^• never \
being assumed invertible. The three steps the source cites are all proved in this library and none \
of them is assumed: the conclusion of Stacks 0DJ9, in the spelling \
`globalBaseChangeIsIsoOfPointwise` (reused verbatim from the Stacks 0A1D module, where it serves \
the same purpose); conclusion (2) of Stacks 0DJA, \
`isIso_baseChangeCohomologyMap_baseChangeSheafHomComparison_of_isPerfect`, at the cartesian \
square; and the stalk check performed inside the proof of Stacks 0A1D, \
`pointwiseBaseChangeOfFlatOver`, that flatness of the terms of 𝒢^• over S gives the condition of \
Stacks 0DJ8 for L(g')^*𝒢^• ⟶ (g')^*𝒢^•. With those three, the qcqs hypothesis on f and the \
cartesian square, the displayed map is an isomorphism. The equivalent conditions of Stacks 0DJ8 \
are used only in form (1), the pointwise condition: forms (2) and (3) are carried in this library \
at the locally small model of D(𝒪_X) rather than at the standard model the map of Stacks 08HY \
lives at, and no implication between them is available. The two D_QCoh memberships Stacks 0DJ9 \
asks of the two derived internal homs are the statement's own conditions hK and hK', at a spelling \
of the derived internal hom that does not line up with the one the comparison map is written at"]
public theorem isIso_sheafHomFlatBaseChangeMap_of_perfect
    {X X' S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
    (hsq : IsPullback g' f' f g) (hqc : QuasiCompact f) (hqs : QuasiSeparated f)
    (w : g' ≫ f = f' ≫ g)
    (sq : g'.toLRSHom.toShHom ≫ f.toLRSHom.toShHom =
      f'.toLRSHom.toShHom ≫ g.toLRSHom.toShHom)
    (E : DerivedCategory X.Modules)
    (hEperfect : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E)
    (G : CochainComplex X.Modules ℤ)
    (hGminus : CochainComplex.minus X.Modules G)
    (hGqcoh : ∀ n : ℤ, (G.X n).IsQuasicoherent)
    (hGflat : ∀ n : ℤ, IsFlatOver f.toLRSHom.toShHom (G.X n))
    (hK : ∀ n : ℤ, ((DerivedCategory.homologyFunctor X.Modules n).obj
      (((derivedSheafHom X.sheaf).obj (op E)).obj
        (DerivedCategory.Q.obj G))).IsQuasicoherent)
    (hK' : ∀ n : ℤ, ((DerivedCategory.homologyFunctor X'.Modules n).obj
      (((derivedSheafHom X'.sheaf).obj
          (op ((derivedPullback g'.toLRSHom.toShHom).obj E))).obj
        (DerivedCategory.Q.obj
          ((pullbackComplex g'.toLRSHom.toShHom).obj G)))).IsQuasicoherent) :
    IsIso (sheafHomFlatBaseChangeMap f g f' g' sq E G) :=
  globalBaseChangeIsIsoOfPointwise f g f' g' hsq hqc hqs w sq _ _ _ hK hK'
    (fun x' n => isIso_baseChangeCohomologyMap_baseChangeSheafHomComparison_of_isPerfect hsq E _
      hEperfect _ _ (pointwiseBaseChangeOfFlatOver f g f' g' hsq w G hGminus hGqcoh hGflat) x' n)

end AlgebraicGeometry

end
