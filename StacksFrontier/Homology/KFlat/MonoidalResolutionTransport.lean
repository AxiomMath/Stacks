module

public import StacksFrontier.Homology.KFlat.BifunctorTransportEquivalence
public import StacksFrontier.Homology.KFlat.MonoidalDerivedTransport

/-!
# K-flat resolutions along a monoidal equivalence

Let `A` and `A'` be abelian monoidal categories whose tensor products are additive in each
variable and admit total tensor complexes, and let `e : A ≌ A'` be an **additive** equivalence
whose functor is **strong monoidal**. If every cochain complex over `A` receives a
quasi-isomorphism from a K-flat one, then so does every cochain complex over `A'`.

That hypothesis is the only one `CochainComplex.KFlatMonoidal.derivedMonoidal` carries, so a
monoidal equivalence transports the derived monoidal structure: a category presented as the
equivalent of one whose K-flat resolutions are known inherits them, with no resolution
constructed on the new side.

## Main results

* `CochainComplex.KFlatBifunctor.exists_kFlat_resolution_of_monoidalEquivalence`: **the
  existence of K-flat resolutions transports along an additive strong monoidal equivalence.**

## Implementation notes

This is `CochainComplex.KFlatBifunctor.exists_kFlat_resolution_of_equivalence` read at the two
tensor bifunctors `CategoryTheory.MonoidalCategory.curriedTensor`, with the abelian-level
comparison `ε` supplied by the monoidality constraint of `e.functor` — exactly the `ε` of
`CochainComplex.KFlatBifunctor.monoidalTransportEps` — and its two naturality squares by
`CategoryTheory.Functor.OplaxMonoidal.δ_natural_left` and `δ_natural_right`. Nothing beyond
strong monoidality of the functor is used; in particular no coherence of `ε` with the
associators is needed, K-flatness being a condition on one pair of slots at a time.

The companion statement for the derived tensor product itself, along the same data, is
`CochainComplex.KFlatBifunctor.monoidalDerivedTransportIso`. It lives in a separate file
because it needs the two localizations as instances, which this statement does not: the
existence of resolutions is what *produces* those localizations, through
`CochainComplex.KFlatBifunctor.kFlatQ_isLocalization`.

**What this does not supply.** A monoidal equivalence is the input; the statement does not
construct one, and for the two categories K-flat resolutions are actually wanted on the
transport does not close.

* For a **functor category** `J ⥤ D`, the hypothesis carried by
  `CategoryTheory.Functor.constMapDerivedCategoryMonoidal` is not an equivalent of a category
  with known resolutions, so no equivalence is available to transport along.
* For the **abelian sheaves** of a topological space — `Stacks.Cohomology.Leray.AbelianSheaf`,
  with the tensor product of `Stacks.Cohomology.Leray.abelianSheafMonoidalCategory` — an
  equivalence *is* available, and to a category where K-flat resolutions are unconditional:
  `Stacks.Cohomology.Leray.abelianSheafIntModulesEquivalence` of
  `StacksFrontier/AlgebraicGeometry/Spaces/AbelianSheafAsIntModules.lean` presents
  `Sheaf (Opens.grothendieckTopology X) AddCommGrpCat` as the sheaves of modules over the
  constant sheaf of rings `ℤ`, which is the structure sheaf of a ringed site, and
  `Stacks.SheafOfModules.exists_kFlat_quasiIso` ([Stacks, Tag 06YS]) resolves every complex
  there. What is missing is one thing, and it is not supplied here: that equivalence is not known
  to carry `Stacks.SheafOfModules.Tensor.sheafTensor` to the tensor product of abelian sheaves,
  so neither this statement nor
  `CochainComplex.KFlatBifunctor.exists_kFlat_resolution_of_equivalence` — which needs only the
  bifunctor comparison, not full monoidality — can be fed. The other presentation, by
  `CategoryTheory.Sheaf.coefficientEquivalence` of
  `StacksFrontier/AlgebraicGeometry/EtaleCohomology/Restriction/CoefficientEquivalence.lean`
  applied to `AddCommGrpCat.uliftIntEquivalence`, which gives
  `Sheaf (Opens.grothendieckTopology X) (ModuleCat (ULift ℤ))`, is a dead end for this purpose:
  no K-flat resolution theorem in this library is about a category of sheaves *valued* in
  modules — they are all for complexes over `ModuleCat R`
  (`CochainComplex.KFlat.exists_kFlat_resolution`, [Stacks, Tag 06Y4]) or for `SheafOfModules`
  over a sheaf of rings on a ringed site. See the module documentation of
  `StacksFrontier/AlgebraicGeometry/Spaces/AbelianSheafMonoidalPreadditive.lean`.

So what is removed here is the generic obstruction — the absence of any transport at all, described in
the module documentation of `StacksFrontier/Homology/ConstMapDerivedCategoryMonoidal.lean`
— and not the two concrete gaps above.

## References

* [Stacks Project, Tag 06Y4](https://stacks.math.columbia.edu/tag/06Y4)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace CochainComplex.KFlatBifunctor

variable {A A' : Type*} [Category A] [Category A'] [Abelian A] [Abelian A']
  [MonoidalCategory A] [MonoidalCategory A']
  [(curriedTensor A).Additive] [∀ X : A, ((curriedTensor A).obj X).Additive]
  [∀ (K₁ K₂ : CochainComplex A ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (curriedTensor A) (ComplexShape.up ℤ)]
  [(curriedTensor A').Additive] [∀ X : A', ((curriedTensor A').obj X).Additive]
  [∀ (K₁ K₂ : CochainComplex A' ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (curriedTensor A') (ComplexShape.up ℤ)]
  (e : A ≌ A') [e.functor.Additive] [e.inverse.Additive] [e.functor.Monoidal]

include e in
/-- **The existence of K-flat resolutions transports along an additive strong monoidal
equivalence.**

If every cochain complex over `A` receives a quasi-isomorphism from a complex K-flat for the
tensor product of `A`, then every cochain complex over `A'` receives one from a complex K-flat
for the tensor product of `A'`. This is the hypothesis `hres` of
`CochainComplex.KFlatMonoidal.derivedMonoidal`, so `D(A')` acquires the derived tensor product
from `D(A)` with no resolution constructed on the `A'` side. -/
theorem exists_kFlat_resolution_of_monoidalEquivalence
    (hres : ∀ G : CochainComplex A ℤ, ∃ (P : CochainComplex A ℤ) (f : P ⟶ G),
      KFlat (curriedTensor A) P ∧ QuasiIso f)
    (G : CochainComplex A' ℤ) :
    ∃ (P : CochainComplex A' ℤ) (f : P ⟶ G),
      KFlat (curriedTensor A') P ∧ QuasiIso f :=
  exists_kFlat_resolution_of_equivalence (curriedTensor A) (curriedTensor A') e
    (monoidalTransportEps e.functor)
    (fun f b => (Functor.OplaxMonoidal.δ_natural_left e.functor f b).symm)
    (fun a {_b _b'} g => (Functor.OplaxMonoidal.δ_natural_right e.functor a g).symm)
    hres G

end CochainComplex.KFlatBifunctor

end
