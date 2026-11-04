module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.BoundedBelowEdgeIsomorphism
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.HomologyComparisonCounit
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.PullbackPushforwardAdjunction

/-!
# Exact functors and the hypercohomology edge morphism

Two facts about an **exact** functor and the edge morphism
`Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.derivedHomologyComparison`, both stated
at the generality the edge morphism itself is defined at — an arbitrary left exact additive
functor of abelian categories, an arbitrary right derived functor of it presented by its unit, and
the existence of K-injective resolutions downstairs as an explicit hypothesis.

*Postcomposition.* If `G` is exact then `G.mapDerivedCategory` is defined, and for any right
derived functor `RF` of a degreewise `F`, the composite `RF ⋙ G.mapDerivedCategory` is a right
derived functor of `F ⋙ G`. The transformation exhibiting it is `exactPostcomposeUnit`: the
comparison of the two readings of `G` on the derived category, followed by the unit of `RF` pushed
along `G`. This is the brick two instances in the tail of [Stacks, Tag 0EX3] (c) were written out
separately before —
`Stacks.EdgeCompat.sectionsOverOpenRestrictCompUnit` (restriction of scalars along a restriction
map of the structure sheaf) and `Stacks.EdgeCompat.preimageSectionsCompUnit` (restriction of
scalars along `f^♯`) — and both are now one application of it.

*Invertibility.* If the functor being derived is itself exact, its edge morphism

> `H^q(RF K) ⟶ F(H^q K)`

is invertible, with **no** K-injectivity, boundedness or acyclicity hypothesis on `K`: exactness
alone. The complex level comparison is invertible for every complex — that is
`Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.isIso_homologyComparison_of_exact`, in
`StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.HomologyComparisonCounit` — and
every object of the derived category is isomorphic to the image of a K-injective complex, where
`isIso_derivedHomologyComparison_app_of_isKInjective` applies.

## Main results

* `Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.exactPostcomposeUnit` and
  `…isRightDerivedFunctor_exactPostcomposeUnit`: **`RF ⋙ G.mapDerivedCategory` derives
  `F ⋙ G` for `G` exact.**
* `Stacks.Cohomology.HypercohomologyEdge.HomologyComparison`
  `.isIso_derivedHomologyComparison_app_of_exact` and
  `…isIso_derivedHomologyComparison_of_exact`: **the edge morphism of an exact functor is
  invertible**, at every object and as a natural transformation.
* `Stacks.Cohomology.HypercohomologyEdge.HomologyComparison`
  `.isIso_derivedHomologyComparison_mapDerivedCategory`: the same at the canonical model
  `G.mapDerivedCategory` with its canonical unit
  `CategoryTheory.Functor.mapDerivedCategoryFactorsh`, which is the model a splitting of the edge
  morphism of a composite leaves behind.

## Implementation notes

*The postcomposition instance is a theorem, not an `instance`.* The existence of K-injective
resolutions is an explicit hypothesis here, as it is on every statement about the edge morphism,
so the conclusion cannot be found by instance search; each call site registers its own one-line
`instance` by supplying its resolutions. That is still the whole content: the call sites carry no
proof.

*The invertibility at an object does not go through the identification of the edge morphism with
`CategoryTheory.Functor.mapDerivedCategoryHomologyIso`.* That identification is **not** proved
here. It would need the complex level statement that
`Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.homologyComparison` — defined by
descending through the cokernel presentation of homology — is the component of
`CategoryTheory.Functor.mapHomologicalComplexHomologyIso`, i.e. of Mathlib's
`CategoryTheory.ShortComplex.homologyFunctorIso`, and no lemma in the library relates the two
presentations. Invertibility is reached without it, from the cokernel presentation directly.

*The complex level input is imported, not reproved here.* The invertibility of
`homologyComparison` at an exact functor and an arbitrary complex is
`isIso_homologyComparison_of_exact` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.HomologyComparisonCounit`, which
this file imports for the step at the K-injective resolution; no induction on the degree and no
acyclicity is involved there either.

## References

* [Stacks Project, Tag 070K](https://stacks.math.columbia.edu/tag/070K)
* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe vA uA vB uB vC uC

namespace Stacks.Cohomology.HypercohomologyEdge.HomologyComparison

variable {A : Type uA} [Category.{vA} A] [Abelian A]
  {B : Type uB} [Category.{vB} B] [Abelian B]

/-! ### An exact functor postcomposed onto a right derived functor -/

section Postcompose

variable {C : Type uC} [Category.{vC} C] [Abelian C]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]

/-- **The unit exhibiting `RF ⋙ G.mapDerivedCategory` as a right derived functor of `F ⋙ G`**,
for `F` additive with right derived functor `RF` presented by `unit` and `G` exact. It is the
comparison of the two readings of `G` on the derived category — `Iso.refl` on the degreewise
functors, then `CategoryTheory.Functor.mapDerivedCategoryFactorsh` — followed by `unit` pushed
along `G`.

The type is written at the composite spelling `(F ⋙ G).mapHomotopyCategory` of the degreewise
functor, which is the spelling the right derived functor is a derived functor *of*. A consumer
whose own degreewise functor is a definitionally equal but differently spelled composite has to
re-type through a `show`; `Stacks.EdgeCompat.preimageSectionsCompUnitComp` is such a
re-registration. -/
def exactPostcomposeUnit (F : A ⥤ B) [F.Additive] (G : B ⥤ C) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (RF : DerivedCategory A ⥤ DerivedCategory B)
    (unit : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF) :
    (F ⋙ G).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF ⋙ G.mapDerivedCategory :=
  ((Functor.isoWhiskerRight
        (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (ComplexShape.up ℤ))
        DerivedCategory.Qh).symm ≪≫
      Functor.isoWhiskerLeft (F.mapHomotopyCategory (ComplexShape.up ℤ))
        G.mapDerivedCategoryFactorsh.symm).hom ≫
    Functor.whiskerRight unit G.mapDerivedCategory

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces in
/-- **`exactPostcomposeUnit` does exhibit a right derived functor**: for `F` additive with a right
derived functor and `G` exact, `RF ⋙ G.mapDerivedCategory` is a right derived functor of
`F ⋙ G`.

By `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces`
`.isRightDerivedFunctor_of_isIso_app_isKInjective` it is enough that the unit be invertible at a
K-injective complex, and there it is the component of an isomorphism followed by `G` applied to
the unit of `RF`, which is invertible at a K-injective complex because `RF` is a right derived
functor ([Stacks, Tag 070K]).

Nothing is assumed of `F` beyond additivity, nothing of `G` beyond exactness, and the K-injective
resolutions are an explicit hypothesis; see the implementation notes on why this is not an
`instance`. -/
theorem isRightDerivedFunctor_exactPostcomposeUnit (F : A ⥤ B) [F.Additive] (G : B ⥤ C)
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (RF : DerivedCategory A ⥤ DerivedCategory B)
    (unit : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor unit (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (hA : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f) :
    (RF ⋙ G.mapDerivedCategory).IsRightDerivedFunctor (exactPostcomposeUnit F G RF unit)
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) := by
  refine isRightDerivedFunctor_of_isIso_app_isKInjective _ hA DerivedCategory.Qh _ _
    fun I hI => ?_
  have hunit : IsIso (unit.app
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)) :=
    (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
      (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) hA).2
      (L := DerivedCategory.Qh) RF unit I hI
  have : IsIso (G.mapDerivedCategory.map
      (unit.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I))) := inferInstance
  rw [exactPostcomposeUnit]
  simp only [NatTrans.comp_app, Functor.whiskerRight_app]
  infer_instance

end Postcompose

/-! ### The edge morphism of an exact functor -/

section Exact

variable (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

variable [HasDerivedCategory A] [HasDerivedCategory B]

/-- **The hypercohomology edge morphism of an exact functor is invertible at every object**, with
exactness the only hypothesis: no K-injectivity, no boundedness and no acyclicity.

Every object of `D(A)` is isomorphic to the image of a K-injective complex — `DerivedCategory.Qh`
is a localization of the homotopy category, so the object is the image of a complex, and `hA`
resolves that complex — and there
`isIso_derivedHomologyComparison_app_of_isKInjective` applies, its complex level hypothesis being
`isIso_homologyComparison_of_exact`.

The right derived functor is arbitrary, presented by its unit; in particular this covers the
canonical model `CategoryTheory.Functor.mapDerivedCategory`, which is
`isIso_derivedHomologyComparison_mapDerivedCategory`. -/
theorem isIso_derivedHomologyComparison_app_of_exact
    (R : DerivedCategory A ⥤ DerivedCategory B)
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ R)
    [R.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (hA : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f) (q : ℤ) (E : DerivedCategory A) :
    IsIso ((derivedHomologyComparison F R α hA q).app E) := by
  have hloc := Localization.essSurj (DerivedCategory.Qh (C := A))
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
  obtain ⟨K, hK⟩ := HomotopyCategory.quotient_obj_surjective
    ((DerivedCategory.Qh (C := A)).objPreimage E)
  obtain ⟨I, f, hI, hf⟩ := hA K
  have : QuasiIso f := hf
  have hiso : IsIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map f)) :=
    Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hf)
  have eE : E ≅ DerivedCategory.Qh.obj
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I) :=
    ((DerivedCategory.Qh (C := A)).objObjPreimageIso E).symm ≪≫
      (DerivedCategory.Qh (C := A)).mapIso (eqToIso hK.symm) ≪≫
      asIso (DerivedCategory.Qh.map
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map f))
  have := isIso_homologyComparison_of_exact F I q
  exact (NatTrans.isIso_app_iff_of_iso _ eE).2
    (isIso_derivedHomologyComparison_app_of_isKInjective F R α hA q I hI)

/-- **The hypercohomology edge morphism of an exact functor is invertible**, as a natural
transformation `R ⋙ H^q ≅ H^q ⋙ F`. Pointwise, by
`isIso_derivedHomologyComparison_app_of_exact`. -/
theorem isIso_derivedHomologyComparison_of_exact
    (R : DerivedCategory A ⥤ DerivedCategory B)
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ R)
    [R.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (hA : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f) (q : ℤ) :
    IsIso (derivedHomologyComparison F R α hA q) := by
  have : ∀ E, IsIso ((derivedHomologyComparison F R α hA q).app E) :=
    fun E => isIso_derivedHomologyComparison_app_of_exact F R α hA q E
  exact NatIso.isIso_of_isIso_app _

/-- **The edge morphism of an exact functor in its canonical model is invertible.** At
`CategoryTheory.Functor.mapDerivedCategory` with the canonical unit
`CategoryTheory.Functor.mapDerivedCategoryFactorsh`, which is the model that splitting the edge
morphism of a composite `F' ⋙ F` leaves in front of the edge morphism of `F'` — see
`Stacks.EdgeCompat.derivedHomologyComparison_comp`. Specialisation of
`isIso_derivedHomologyComparison_of_exact`; the hypothesis is still exactness alone. -/
theorem isIso_derivedHomologyComparison_mapDerivedCategory
    [F.mapDerivedCategory.IsRightDerivedFunctor F.mapDerivedCategoryFactorsh.inv
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (hA : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f) (q : ℤ) :
    IsIso (derivedHomologyComparison F F.mapDerivedCategory
      F.mapDerivedCategoryFactorsh.inv hA q) :=
  isIso_derivedHomologyComparison_of_exact F _ _ hA q

end Exact

end Stacks.Cohomology.HypercohomologyEdge.HomologyComparison

end
