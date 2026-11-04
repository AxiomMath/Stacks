module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackOfRingedTopoi
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.DistinguishedTriangles
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionWithFlatTerms
public import StacksFrontier.Homology.KFlat.Resolution
import StacksCore.Tactic.StacksAttribute

/-!
# Factoring a map out of a K-flat complex through a quasi-isomorphism

Let `(X, O_X)` be a ringed space and let `a : K^• ⟶ L^•` be a map of complexes of
`O_X`-modules with `K^•` K-flat. Then `a` factors, up to homotopy, as `K^• ⟶ N^• ⟶ L^•`
with `N^•` K-flat and `N^• ⟶ L^•` a quasi-isomorphism; and if the terms of `K^•` are flat
then `N^•` can be chosen with flat terms as well.

The proof is the one in the source. Choose a K-flat resolution `q : M^• ⟶ C(a)` of the
mapping cone of `a` whose terms are flat (Tag 06YS, which for a ringed space is Tag 06YF),
and let `N^•` be the extension of `K^•` by `M^•` twisted by the first component of `q`:
degreewise the biproduct `K^i ⊞ M^i`, with the differential of the biproduct corrected by the
twisting cochain. That extension sits in a degreewise split short exact sequence
`0 ⟶ K^• ⟶ N^• ⟶ M^• ⟶ 0`, hence in a distinguished triangle of `K(Mod(O_X))`, and it comes
with a map `c : N^• ⟶ L^•` extending `a` which is a quasi-isomorphism because `q` is. K-flatness
of `N^•` is then two-out-of-three in that triangle (Tag 079S), and flatness of its terms is
flatness of a binary biproduct of flat modules.

## Main results

* `Stacks.SheafOfModules.exists_isKFlat_factorization`: the factorization.
* `Stacks.SheafOfModules.exists_isKFlat_isFlat_factorization`: the factorization with flat
  terms, when the source has flat terms.

## Implementation notes

The statements are for a ringed site, which includes the ringed space of the source: a ringed
space is a topological space together with a sheaf of commutative rings on the site of its
open subsets, and a sheaf of `O_X`-modules is a `SheafOfModules` over the underlying sheaf of
rings of that site. Being stated for a ringed site, they are at the same time Tag 0G7D, whose
statement is Tag 0G6V's with "ringed space" replaced by "ringed site"; both tags are therefore
registered on the same two declarations and no copy of the factorization is made for the site
case.

The twisted extension and the quasi-isomorphism out of it are not rebuilt here. They are
`CochainComplex.KFlat.exists_factorization_of_quasiIso_toMappingCone`, which performs the
construction in an arbitrary abelian category and hands back exactly the three further pieces
of data needed to transfer properties of `K^•` and `M^•` to `N^•`: the factorization, the
distinguished triangle on `(K^•, N^•, M^•)`, and the termwise biproduct decomposition of
`N^•`. Flatness of a binary biproduct is
`Stacks.Sheaves.RingedToposDerivedPullback.isFlat_biprod`.

The two existence statements are separate because the flat-terms conclusion needs an extra
hypothesis; in each of them all the asserted properties hold for one and the same choice of
`N^•`, `b` and `c`, which is what the source asserts. `Homotopy` is Mathlib's type of chain
homotopies, and the homotopy produced here is in fact the one coming from an equality — the
factorization holds on the nose — but it is the homotopy that is asserted, as in the source.

**Universes.** All four universes are tied to a single `u` and the site is small. This is
inherited from the existence of K-flat resolutions with flat terms,
`Stacks.SheafOfModules.exists_kFlatResolution`, which is where Tag 06YS pins them, and is not
introduced here.

## References

* [Stacks Project, Tag 0G6V](https://stacks.math.columbia.edu/tag/0G6V)
* [Stacks Project, Tag 0G7D](https://stacks.math.columbia.edu/tag/0G7D)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 079S](https://stacks.math.columbia.edu/tag/079S)
* [Stacks Project, Tag 05NG](https://stacks.math.columbia.edu/tag/05NG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.SheafOfModules

variable (X : AlgebraicGeometry.RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- Both halves of Tag 0G6V at once: the factorization, together with the implication that
makes the terms of the intermediate complex flat when the terms of the source are. The two
public statements are the two halves of this one, which is proved once so that they are
realized by the same `N`, `b` and `c`. -/
private theorem factorizationData
    {K L : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) ℤ}
    (a : K ⟶ L) (hK : IsKFlat X.O K) :
    ∃ (N : CochainComplex
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) ℤ)
      (b : K ⟶ N) (c : N ⟶ L),
      IsKFlat X.O N ∧ QuasiIso c ∧ Nonempty (Homotopy a (b ≫ c)) ∧
        ((∀ i : ℤ,
            AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.O) (K.X i)) →
          ∀ i : ℤ,
            AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.O) (N.X i)) := by
  obtain ⟨M, q, hM, hMflat, hq, -⟩ := exists_kFlatResolution X (CochainComplex.mappingCone a)
  obtain ⟨N, b, g, c, e, δ, hbc, hc, hT⟩ :=
    CochainComplex.KFlat.exists_factorization_of_quasiIso_toMappingCone a q hq
  refine ⟨N, b, c, ?_, hc, ⟨Homotopy.ofEq hbc.symm⟩, fun hKflat i => ?_⟩
  · exact kFlat_of_first_third X.O _ _ _ hT hK hM
  · exact AlgebraicGeometry.SheafOfModules.IsFlat.of_iso X.O (e i).symm
      (Stacks.Sheaves.RingedToposDerivedPullback.isFlat_biprod X.O (K.X i) (M.X i)
        (hKflat i) (hMflat i))

/-- **Tag 0G6V.** A map `a : K^• ⟶ L^•` of complexes of `O`-modules with `K^•` K-flat factors,
up to homotopy, through a K-flat complex `N^•` which maps to `L^•` by a quasi-isomorphism. -/
@[stacks 0G6V "the K-flat factorization", stacks 0G7D "the K-flat factorization"]
theorem exists_isKFlat_factorization
    {K L : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) ℤ}
    (a : K ⟶ L) (hK : IsKFlat X.O K) :
    ∃ (N : CochainComplex
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) ℤ)
      (b : K ⟶ N) (c : N ⟶ L),
      IsKFlat X.O N ∧ QuasiIso c ∧ Nonempty (Homotopy a (b ≫ c)) := by
  obtain ⟨N, b, c, hN, hc, ha, -⟩ := factorizationData X a hK
  exact ⟨N, b, c, hN, hc, ha⟩

/-- **Tag 0G6V, second half.** If in addition the terms of `K^•` are flat `O`-modules, then the
intermediate complex of the factorization can be chosen with flat terms as well. -/
@[stacks 0G6V "the factorization with flat terms",
  stacks 0G7D "the factorization with flat terms"]
theorem exists_isKFlat_isFlat_factorization
    {K L : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) ℤ}
    (a : K ⟶ L) (hK : IsKFlat X.O K)
    (hKflat : ∀ i : ℤ,
      AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.O) (K.X i)) :
    ∃ (N : CochainComplex
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) ℤ)
      (b : K ⟶ N) (c : N ⟶ L),
      IsKFlat X.O N ∧
        (∀ i : ℤ,
          AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.O) (N.X i)) ∧
        QuasiIso c ∧ Nonempty (Homotopy a (b ≫ c)) := by
  obtain ⟨N, b, c, hN, hc, ha, hflat⟩ := factorizationData X a hK
  exact ⟨N, b, c, hN, hflat hKflat, hc, ha⟩

end Stacks.SheafOfModules
