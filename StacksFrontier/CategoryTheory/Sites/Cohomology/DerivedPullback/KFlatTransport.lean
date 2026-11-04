module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.KFlatPullbackOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.FlatTransport
public import StacksFrontier.Homology.KFlat.BifunctorBoundedAbove

/-!
# K-flatness with flat terms transports along an isomorphism of complexes

`Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat` — the resolving class of the
derived pullback on a ringed topos — is the conjunction of K-flatness of the chosen
representative complex and flatness of each of its terms. The second conjunct is a condition on
the *representative*, so the property is not invariant under an isomorphism of the homotopy
category. It *is* invariant under an isomorphism of the representing complexes, and that is what
this module records.

## Main results

* `Stacks.Sheaves.DerivedPullback.KFlatTransport.isFlat_X_of_iso`: the flat-terms clause
  transports along an isomorphism of complexes.
* `Stacks.Sheaves.DerivedPullback.KFlatTransport.isKFlat_of_iso`: `IsKFlat` transports along an
  isomorphism of the representing complexes.
* `Stacks.Sheaves.DerivedPullback.KFlatTransport.isKFlat_mapHomotopyCategory_of_natIso`: two
  additive functors of sheaves of modules compared by a natural isomorphism have the same
  degreewise images in the class.

## Implementation notes

Neither clause needs new mathematics: `CochainComplex.KFlatBifunctor.KFlat.of_iso` transports the
first and `AlgebraicGeometry.SheafOfModules.IsFlat.of_iso` the second, the latter at each term
through `HomologicalComplex.eval`. What the tree lacked is the statement about the pair, and the
form in which a consumer meets it: a complex obtained by applying an additive functor to a
complex, where the comparison of two such functors is a natural isomorphism and not an equality.

The flat-terms clause is split off as its own lemma. Supplied inline, the term `IsFlat` of a
degree of an isomorphic complex is elaborated against an expected type whose sheaf of rings is
still the one of the ambient ringed topos rather than the `Tensor` spelling that
`AlgebraicGeometry.SheafOfModules.IsFlat.of_iso` is stated over, and the unification of the two
spellings inside the larger application does not terminate inside the budget; at one degree it
is immediate.

## References

* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 06YN](https://stacks.math.columbia.edu/tag/06YN)
* [Stacks Project, Tag 03ER](https://stacks.math.columbia.edu/tag/03ER)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace Stacks.Sheaves.DerivedPullback.KFlatTransport

variable {Y : RingedTopos.{u, u, u}}
  [Y.J.HasSheafCompose (forget RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

omit [Y.J.HasSheafCompose (forget RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})] in
/-- **The flat-terms clause transports along an isomorphism of complexes.** In each degree the
isomorphism of complexes has an isomorphism of modules as its component, and flatness of a sheaf
of modules is a property of its isomorphism class. -/
theorem isFlat_X_of_iso
    {K L : CochainComplex
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))) ℤ}
    (e : K ≅ L)
    (hK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i))
    (i : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (L.X i) :=
  AlgebraicGeometry.SheafOfModules.IsFlat.of_iso.{u} Y.O
    ((HomologicalComplex.eval _ (ComplexShape.up ℤ) i).mapIso e) (hK i)

omit [Y.J.HasSheafCompose (forget RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})] in
/-- **K-flatness with flat terms transports along an isomorphism of the representing
complexes.** Both clauses transport: the K-flatness of the complex by
`CochainComplex.KFlatBifunctor.KFlat.of_iso` and the flatness of its terms by
`Stacks.Sheaves.DerivedPullback.KFlatTransport.isFlat_X_of_iso`. -/
theorem isKFlat_of_iso
    {M N : HomotopyCategory
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O)))
      (ComplexShape.up ℤ)}
    (hM : Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat (Y := Y) M)
    (e : M.as ≅ N.as) :
    Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat (Y := Y) N :=
  ⟨CochainComplex.KFlatBifunctor.KFlat.of_iso _ hM.1 e, isFlat_X_of_iso e hM.2⟩

variable {Z : RingedTopos.{u, u, u}}
  [Z.J.HasSheafCompose (forget RingCat.{u})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify Z.J AddCommGrpCat.{u}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

omit [Y.J.HasSheafCompose (forget RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Z.J.HasSheafCompose (forget RingCat.{u})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify Z.J AddCommGrpCat.{u}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The class of K-flat complexes with flat terms sees a functor only up to isomorphism.** If
two additive functors of sheaves of modules are naturally isomorphic, then the degreewise image
of a complex under the one is K-flat with flat terms as soon as the degreewise image under the
other is.

This is the form a consumer needs: two presentations of one and the same construction on sheaves
of modules are compared by a natural isomorphism, and the class is indexed by objects of the
homotopy category, whose representative of an image is the image of the representative on the
nose. -/
theorem isKFlat_mapHomotopyCategory_of_natIso
    (F G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Z.J) Z.O)) ⥤
      SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O)))
    [F.Additive] [G.Additive] (e : F ≅ G)
    (K : HomotopyCategory
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Z.J) Z.O)))
      (ComplexShape.up ℤ))
    (hK : Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat (Y := Y)
      ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K)) :
    Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat (Y := Y)
      ((G.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) :=
  isKFlat_of_iso hK ((NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).app K.as)

end Stacks.Sheaves.DerivedPullback.KFlatTransport

end

end
