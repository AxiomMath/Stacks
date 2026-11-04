module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.ModuliEllipticCurvesBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.ModuliEllipticCurvesGluing
public import StacksFrontier.AlgebraicGeometry.Stacks.WeierstrassCoordinateChangeTorsor
public import StacksFrontier.AlgebraicGeometry.Stacks.WeierstrassEquationNoetherian

/-!
# The fibre product of two morphisms to the moduli stack of elliptic curves is a scheme

Let `E` be an elliptic curve over `S` and `E'` an elliptic curve over `S'`, that is, two
morphisms `S ⟶ 𝓜₁,₁` and `S' ⟶ 𝓜₁,₁`. The fibre product `S ×_{𝓜₁,₁} S'` is the functor sending a
scheme `T` to the triples `(a, a', α)` of
`StacksFrontier/AlgebraicGeometry/Stacks/ModuliEllipticCurves.lean`, and the key fact, Tag 072M, is
that this functor is representable by a scheme.

The source indicates a proof through the relative isomorphism functor
`Isom_{S × S'}(E × S', S × E')` and Grothendieck's Hilbert schemes. The proof here uses Weierstrass
equations instead, which describe that functor explicitly. Let `W` be the scheme of Weierstrass
equations with invertible discriminant and `H` the group scheme of coordinate changes.

* Over `W × W` the functor is represented by `H × W`: the isomorphisms between the two pulled-back
  Weierstrass curves are exactly the coordinate changes between the two equations
  (`AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.representsComparisons_coordinateChange`).
* Every elliptic curve is, Zariski locally on its base, the restriction of the Weierstrass family
  along a morphism to `W`
  (`AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.localWeierstrassAt_of_noetherian` with
  `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.localWeierstrassNoetherian`).
* So over a product `U × U'` of such opens the functor is represented by a base change of `H × W`
  (`AlgebraicGeometry.ModuliEllipticCurves.RepresentsComparisons.ofComparisons`), and these local
  representing schemes glue, because the functor is a Zariski sheaf
  (`AlgebraicGeometry.ModuliEllipticCurves.exists_representsComparisons_of_openCover`).

## Main results

* `AlgebraicGeometry.ModuliEllipticCurves.exists_representsComparisons_of_hasLocalComparison`:
  families which are Zariski locally restrictions of two families with a fibre product have a
  fibre product.
* `AlgebraicGeometry.ModuliEllipticCurves.exists_representsComparisons`: the key fact, Tag 072M.
* `AlgebraicGeometry.ModuliEllipticCurves.keyFactHolds`: condition (2) of Tag 072R.

## References

* [Stacks Project, Tag 072L](https://stacks.math.columbia.edu/tag/072L)
* [Stacks Project, Tag 072M](https://stacks.math.columbia.edu/tag/072M)
* [Stacks Project, Tag 072R](https://stacks.math.columbia.edu/tag/072R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.ModuliEllipticCurves

variable {S S' : Scheme.{u}}

/-! ### Families which are locally restrictions of families with a fibre product -/

/-- **A fibre product over `𝓜₁,₁` from local presentations.** If `P` is a fibre product for
`(F, F')`, and the families `E` over `S` and `E'` over `S'` are, Zariski locally on their bases,
restrictions of `F` and `F'`, then `E` and `E'` have a fibre product. Over the products of the
opens of the two presentations it is the base change of `P`
(`RepresentsComparisons.ofComparisons`), and these glue
(`exists_representsComparisons_of_openCover`). -/
theorem exists_representsComparisons_of_hasLocalComparison {W W' P : Scheme.{u}}
    {F : PointedFamily W} {F' : PointedFamily W'} (r : RepresentsComparisons F F' P)
    (E : PointedFamily S) (E' : PointedFamily S') (hE : ∀ s : S, HasLocalComparison F E s)
    (hE' : ∀ s : S', HasLocalComparison F' E' s) :
    ∃ Q : Scheme.{u}, Nonempty (RepresentsComparisons E E' Q) := by
  choose U hU x hx using hE
  choose U' hU' x' hx' using hE'
  refine exists_representsComparisons_of_openCover E E' U
    (eq_top_iff.2 fun s _ => TopologicalSpace.Opens.mem_iSup.2 ⟨s, hU s⟩) U'
    (eq_top_iff.2 fun s _ => TopologicalSpace.Opens.mem_iSup.2 ⟨s, hU' s⟩) fun i j => ?_
  exact ⟨_, ⟨r.ofComparisons (x i) (x' j) (hx i) (hx' j)⟩⟩

/-! ### The key fact -/

/-- **Stacks Project, Tag 072M.** *Key fact.* For elliptic curves `E` over `S` and `E'` over `S'`,
the functor sending a scheme `T` to the triples `(a, a', α)` is representable by a scheme, the
fibre product `S ×_{𝓜₁,₁} S'`. -/
@[stacks 072M]
theorem exists_representsComparisons (E : PointedFamily S) (E' : PointedFamily S')
    (hE : E.IsElliptic) (hE' : E'.IsElliptic) :
    ∃ P : Scheme.{u}, Nonempty (RepresentsComparisons E E' P) :=
  exists_representsComparisons_of_hasLocalComparison
    Weierstrass.representsComparisons_coordinateChange E E'
    (Weierstrass.localWeierstrassAt_of_noetherian Weierstrass.localWeierstrassNoetherian E hE)
    (Weierstrass.localWeierstrassAt_of_noetherian Weierstrass.localWeierstrassNoetherian E' hE')

/-- **Stacks Project, Tag 072R**, condition (2): the key fact holds. -/
theorem keyFactHolds : KeyFactHolds.{u} := fun E E' hE hE' =>
  exists_representsComparisons E E' hE hE'

end AlgebraicGeometry.ModuliEllipticCurves

end
