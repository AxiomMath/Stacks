module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackOfKFlatComplexes
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.BoundedBelowFlatRepresentative
public import StacksFrontier.CategoryTheory.Sites.Modules.LocalizationRingedSites.Morphism
import StacksCore.Tactic.StacksAttribute

/-!
# The pullback-stability clause of Stacks 0F1M

Let `(C, O)` be a ringed site, `T` a derived tensor product on `D(O)`, and `a` an integer.
`Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitudeGE_iff_exists_kFlatRepresentative` is
Stacks 0F1M's equivalence: an object `E` of `D(O)` has Tor amplitude in `[a, ∞]` exactly when it
is represented by a K-flat complex of flat `O`-modules vanishing in every degree below `a`. The
source adds a "moreover": the representative may be chosen so that its pullback along any
morphism of ringed topoi is *again* K-flat *and again* has flat terms. This file states that
clause, with both of its halves.

## Main results

* `DerivedTensorProduct.exists_pullbackStable_kFlatRepresentative_of_hasTorAmplitudeGE`:
  **Stacks 0F1M, the "moreover" clause.** An object of Tor amplitude in `[a, ∞]` has a
  representative which is K-flat with flat terms, vanishes below `a`, and whose degreewise
  pullback along every morphism of ringed topoi presented by a morphism of sites is K-flat with
  flat terms.

## Implementation notes

*No choice is in fact involved, and the statement records that.* By Stacks 0G7E the degreewise
pullback of *any* K-flat complex with flat terms is K-flat with flat terms, so the pullback
clause holds of every representative as in part (2) of the equivalence rather than of some
specially chosen one. The statement below therefore carries the clause as a further conjunct of
the same existential, obtained from the representative
`Stacks.SheafOfModules.DerivedTensorProduct.exists_kFlatRepresentative_of_hasTorAmplitudeGE`
already produces: nothing about that complex is re-chosen here.

*Why the target of the pullback is a `RingedTopos`.* The two halves of Stacks 0G7E are
`AlgebraicGeometry.RingedToposSiteHom.kFlat_pullbackComplex` and
`AlgebraicGeometry.RingedToposSiteHom.isFlat_pullbackComplex_X`, stated for a morphism of ringed
topoi whose geometric half is presented by a continuous functor of the underlying sites. The
ringed site `(C, O)` is read as a ringed topos by `AlgebraicGeometry.RingedSite.ringedTopos`,
which keeps the same site and the same structure sheaf, so the categories of modules — and hence
the complex `K` — are unchanged.

*Universes.* All collapsed to one, as in the equivalence and in Stacks 0G7E.

## References

* [Stacks Project, Tag 0F1M](https://stacks.math.columbia.edu/tag/0F1M)
* [Stacks Project, Tag 0G7E](https://stacks.math.columbia.edu/tag/0G7E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u d

namespace Stacks.SheafOfModules.DerivedTensorProduct

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable {X : RingedSite.{u, u, u}}
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{d} (RingedSite.Modules.{u, u, u} X)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules.{u, u, u} X) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- **Stacks 0F1M, the "moreover" clause.** An object `E` of `D(O)` with Tor amplitude in
`[a, ∞]` is represented by a complex `K` which is K-flat, has flat terms and vanishes in every
degree below `a`, and which *moreover* stays K-flat with flat terms under pullback: for every
morphism `f` of ringed topoi into `(C, O)` presented by a morphism of sites, the degreewise
pullback `f^*K` is K-flat and each of its terms is flat.

Both halves of the "moreover" are the two halves of Stacks 0G7E, applied to the representative
produced by
`Stacks.SheafOfModules.DerivedTensorProduct.exists_kFlatRepresentative_of_hasTorAmplitudeGE`;
since 0G7E needs nothing of `K` beyond K-flatness and flatness of the terms, no choice of
representative is involved. The tag is registered on its instance at the constructed derived
tensor product,
`Stacks.SheafOfModules.exists_pullbackStable_kFlatRepresentative_of_hasTorAmplitudeGE`. -/
theorem exists_pullbackStable_kFlatRepresentative_of_hasTorAmplitudeGE
    (T : DerivedTensorProduct.{u, u, u, d} X)
    (E : RingedSite.DerivedModules.{u, u, u, d} X) (a : ℤ) (hE : HasTorAmplitudeGE T E a) :
    ∃ K : CochainComplex (RingedSite.Modules.{u, u, u} X) ℤ,
      IsKFlat X.O K ∧
      (∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.O) (K.X i)) ∧
      (∀ i : ℤ, i < a → IsZero (K.X i)) ∧
      Nonempty (DerivedCategory.Q.obj K ≅ E) ∧
      ∀ (X' : AlgebraicGeometry.RingedTopos.{u, u, u})
        [HasSheafify X'.J AddCommGrpCat.{u}]
        [X'.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
        [(Stacks.SheafOfModules.Tensor.sheafTensor X'.O).Additive]
        [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor X'.O).obj M).Additive]
        [∀ (K₁ K₂ : CochainComplex
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O)) ℤ),
          HomologicalComplex.HasMapBifunctor K₁ K₂
            (Stacks.SheafOfModules.Tensor.sheafTensor X'.O) (ComplexShape.up ℤ)]
        (f : AlgebraicGeometry.RingedToposSiteHom X' (RingedSite.ringedTopos X)),
        f.u.IsMorphismOfSites (RingedSite.ringedTopos X).J X'.J →
          IsKFlat X'.O
              ((Stacks.Sheaves.DerivedPullback.KFlatPullback.pullbackComplex f).obj K) ∧
            ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X'.O)
              (((Stacks.Sheaves.DerivedPullback.KFlatPullback.pullbackComplex f).obj K).X i) := by
  obtain ⟨K, hKflat, hflat, hzero, he⟩ :=
    exists_kFlatRepresentative_of_hasTorAmplitudeGE T E a hE
  exact ⟨K, hKflat, hflat, hzero, he, fun X' _ _ _ _ _ f hmos =>
    ⟨AlgebraicGeometry.RingedToposSiteHom.kFlat_pullbackComplex f hmos K hKflat hflat,
      AlgebraicGeometry.RingedToposSiteHom.isFlat_pullbackComplex_X f hmos K hflat⟩⟩

end Stacks.SheafOfModules.DerivedTensorProduct

end
