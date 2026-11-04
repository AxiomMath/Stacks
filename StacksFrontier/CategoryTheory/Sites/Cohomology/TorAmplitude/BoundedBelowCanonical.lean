module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Existence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.PullbackStableFlatRepresentative
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 0F1M for the constructed derived tensor product

Let `(C, O)` be a ringed site, `E` an object of `D(O)` and `a` an integer. Stacks 0F1M says that
`E` has Tor amplitude in `[a, ∞]` exactly when it is represented by a K-flat complex of flat
`O`-modules vanishing in every degree below `a`, and that such a representative may moreover be
chosen so that its pullback along every morphism of ringed sites is again K-flat with flat terms.

Tor amplitude is read off the derived tensor product `- ⊗^L_O -` of `D(O)`. This file states the
tag for the derived tensor product the library *constructs*, Stacks 06YU's
`Stacks.SheafOfModules.canonicalDerivedTensorProduct` (proved to exist by
`Stacks.SheafOfModules.exists_derivedTensorProduct`), so that nothing about the derived tensor
product — its existence, its comparison with the total tensor complex on K-flat representatives,
or its exactness — is a hypothesis of the statements here.

## Main results

* `Stacks.SheafOfModules.hasTorAmplitudeGE_iff_exists_kFlatRepresentative`:
  **Stacks 0F1M, the equivalence.**
* `Stacks.SheafOfModules.exists_pullbackStable_kFlatRepresentative_of_hasTorAmplitudeGE`:
  **Stacks 0F1M, the "moreover" clause.**

## Implementation notes

Both are the instances at `canonicalDerivedTensorProduct X` of the statements (in the namespace
`Stacks.SheafOfModules`) `DerivedTensorProduct.hasTorAmplitudeGE_iff_exists_kFlatRepresentative`
and `DerivedTensorProduct.exists_pullbackStable_kFlatRepresentative_of_hasTorAmplitudeGE`, which
are proved for an arbitrary element of `Stacks.SheafOfModules.DerivedTensorProduct`. The universes
are those of those statements: the site, its structure sheaf and its modules in one universe `u`,
the derived category's hom universe `d` free. At that single universe the site is small, and every
piece of sheafification, additivity and totalisation infrastructure which the general statements
carry as hypotheses — for `(C, O)` and for the source of the pullback — is an instance, so none of
it is assumed: only `HasDerivedCategory.{d}`, which names the hom universe of the localization,
remains, as in Stacks 08G1's
`DerivedTensorProduct.hasTorAmplitude_canonical_iff_exists_flatRepresentative`.

## References

* [Stacks Project, Tag 0F1M](https://stacks.math.columbia.edu/tag/0F1M)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u d

namespace Stacks.SheafOfModules

variable {X : RingedSite.{u, u, u}} [HasDerivedCategory.{d} (RingedSite.Modules.{u, u, u} X)]

/-- **Stacks 0F1M.** Let `(C, O)` be a ringed site, `E` an object of `D(O)` and `a` an integer.
Then `E` has Tor amplitude in `[a, ∞]` for the derived tensor product of `D(O)` — that is,
`E ⊗^L_O F[0]` has no cohomology below `a` for every `O`-module `F` — if and only if `E` is
represented by a K-flat complex of flat `O`-modules vanishing in every degree below `a`. -/
@[stacks 0F1M "equivalence"]
theorem hasTorAmplitudeGE_iff_exists_kFlatRepresentative
    (E : RingedSite.DerivedModules.{u, u, u, d} X) (a : ℤ) :
    letI : X.J.WEqualsLocallyBijective AddCommGrpCat.{u} := inferInstance
    DerivedTensorProduct.HasTorAmplitudeGE (canonicalDerivedTensorProduct.{u, u, d} X) E a ↔
      ∃ K : CochainComplex (RingedSite.Modules.{u, u, u} X) ℤ,
        IsKFlat X.O K ∧
        (∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.O) (K.X i)) ∧
        (∀ i : ℤ, i < a → IsZero (K.X i)) ∧
        Nonempty (DerivedCategory.Q.obj K ≅ E) :=
  let : X.J.WEqualsLocallyBijective AddCommGrpCat.{u} := inferInstance
  DerivedTensorProduct.hasTorAmplitudeGE_iff_exists_kFlatRepresentative
    (canonicalDerivedTensorProduct.{u, u, d} X) E a

/-- **Stacks 0F1M, the "moreover" clause.** An object `E` of `D(O)` with Tor amplitude in
`[a, ∞]` for the derived tensor product of `D(O)` is represented by a complex `K` which is
K-flat, has flat terms and vanishes in every degree below `a`, and which moreover stays K-flat
with flat terms under pullback: for every morphism `f` of ringed topoi into `(C, O)` presented
by a morphism of sites, the degreewise pullback `f^*K` is K-flat and each of its terms is
flat. -/
@[stacks 0F1M "the Moreover clause: the representative stays K-flat, and keeps flat terms, under
pullback"]
theorem exists_pullbackStable_kFlatRepresentative_of_hasTorAmplitudeGE
    (E : RingedSite.DerivedModules.{u, u, u, d} X) (a : ℤ)
    (hE :
      letI : X.J.WEqualsLocallyBijective AddCommGrpCat.{u} := inferInstance
      DerivedTensorProduct.HasTorAmplitudeGE
        (canonicalDerivedTensorProduct.{u, u, d} X) E a) :
    letI : X.J.WEqualsLocallyBijective AddCommGrpCat.{u} := inferInstance
    ∃ K : CochainComplex (RingedSite.Modules.{u, u, u} X) ℤ,
      IsKFlat X.O K ∧
      (∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.O) (K.X i)) ∧
      (∀ i : ℤ, i < a → IsZero (K.X i)) ∧
      Nonempty (DerivedCategory.Q.obj K ≅ E) ∧
      ∀ X' : AlgebraicGeometry.RingedTopos.{u, u, u},
        letI : X'.J.WEqualsLocallyBijective AddCommGrpCat.{u} := inferInstance
        ∀ f : AlgebraicGeometry.RingedToposSiteHom X' (RingedSite.ringedTopos X),
          f.u.IsMorphismOfSites (RingedSite.ringedTopos X).J X'.J →
            IsKFlat X'.O
                ((Stacks.Sheaves.DerivedPullback.KFlatPullback.pullbackComplex f).obj K) ∧
              ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X'.O)
                (((Stacks.Sheaves.DerivedPullback.KFlatPullback.pullbackComplex f).obj K).X i) :=
  let : X.J.WEqualsLocallyBijective AddCommGrpCat.{u} := inferInstance
  by
    obtain ⟨K, hKflat, hflat, hzero, he, hpull⟩ :=
      DerivedTensorProduct.exists_pullbackStable_kFlatRepresentative_of_hasTorAmplitudeGE
        (canonicalDerivedTensorProduct.{u, u, d} X) E a hE
    refine ⟨K, hKflat, hflat, hzero, he, fun X' => ?_⟩
    let : X'.J.WEqualsLocallyBijective AddCommGrpCat.{u} := inferInstance
    exact fun f hf => hpull X' f hf

end Stacks.SheafOfModules

end
