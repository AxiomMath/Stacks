module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.BoundedAboveCohomology
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RelativeBoundedComplex

/-!
# A locally bounded above object with relatively pseudo-coherent cohomology sheaves

Let `f : X ⟶ S` be a morphism of schemes locally of finite type and let `E` be an object of
`D(𝒪_X)` whose cohomology sheaves vanish in high degrees on a neighbourhood of every point. If
`H^i(E)` is `(m - i)`-pseudo-coherent relative to `S` for every `i`, then `E` is
`m`-pseudo-coherent relative to `S`. This is Stacks 09UQ.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_of_homology_of_locally_boundedAbove`:
  if the cohomology sheaves of a locally bounded above `E` are relatively
  `(m - i)`-pseudo-coherent, then `E` is relatively `m`-pseudo-coherent.

## Implementation notes

The derived categories are the ones provided by `CategoryTheory.HasDerivedCategory.standard`,
which is made a local instance; there is no global instance, so a user of this result makes the
same declaration.

## References

* [The Stacks Project, Lemma 36.61.10 (09UQ)](https://stacks.math.columbia.edu/tag/09UQ)
* [The Stacks Project, Definition 36.61.1 (09UI)](https://stacks.math.columbia.edu/tag/09UI)
* [The Stacks Project, Lemma 36.61.5 (09UJ)](https://stacks.math.columbia.edu/tag/09UJ)
* [The Stacks Project, Lemma 36.61.2 (09VC)](https://stacks.math.columbia.edu/tag/09VC)
* [The Stacks Project, Lemma 36.61.9 (09UP)](https://stacks.math.columbia.edu/tag/09UP)
* [The Stacks Project, Lemma 20.46.15 (09V8)](https://stacks.math.columbia.edu/tag/09V8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

namespace Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- Let `f : X ⟶ S` be a morphism of schemes locally of finite type, let `m` be an integer and let
`E` be an object of `D(𝒪_X)` whose cohomology sheaves vanish in high degrees on a neighbourhood of
every point. If `H^i(E)` is `(m - i)`-pseudo-coherent relative to `S` for every `i`, then `E` is
`m`-pseudo-coherent relative to `S`. -/
@[stacks 09UQ]
public theorem isPseudoCoherentFrom_of_homology_of_locally_boundedAbove [LocallyOfFiniteType f]
    (m : ℤ) (E : DerivedCategory X.Modules)
    (hbdd : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∃ b : ℤ, ∀ i : ℤ, b < i →
      IsZero ((Scheme.Modules.restrictFunctor U.ι).obj
        ((DerivedCategory.homologyFunctor X.Modules i).obj E)))
    (hcoh : ∀ i : ℤ, IsModulePseudoCoherentFrom f
      ((DerivedCategory.homologyFunctor X.Modules i).obj E) (m - i)) :
    IsPseudoCoherentFrom f E m := by
  refine isPseudoCoherentFrom_of_forall_affinePair f E m fun U V hUV => ?_
  obtain ⟨n, i, hi, hio⟩ := exists_isClosedImmersion_affineSpace_resLE f V U hUV
  have := hi
  refine ⟨n, i, hi, hio, (Scheme.Modules.isPseudoCoherentFromAfterPushforward_iff i _ _).2 ?_⟩
  obtain ⟨B, hB⟩ := exists_isZero_restrict_of_isCompact
    (fun j => (DerivedCategory.homologyFunctor X.Modules j).obj E) U.1 U.2.isCompact
    fun x _ => hbdd x
  set R := Scheme.Modules.restrictFunctor U.1.ι with hR
  set P := Scheme.Modules.pushforward i with hP
  have ehom : ∀ j : ℤ, (DerivedCategory.homologyFunctor _ j).obj
      (P.mapDerivedCategory.obj (R.mapDerivedCategory.obj E)) ≅
        P.obj (R.obj ((DerivedCategory.homologyFunctor X.Modules j).obj E)) := fun j =>
    P.mapDerivedCategoryObjHomologyIso (R.mapDerivedCategory.obj E) j ≪≫
      P.mapIso (R.mapDerivedCategoryObjHomologyIso E j)
  refine RingedSpace.isPseudoCoherentFrom_of_homology_of_boundedAbove.{u + 1, u} m B _
    (fun j hj => (Functor.map_isZero P (hB j hj)).of_iso (ehom j)) fun j _ => ?_
  have h0 := (Scheme.Modules.isPseudoCoherentFromAfterPushforward_iff i _ _).1
    (IsPseudoCoherentFromOnAffinePair.forall_isClosedImmersion f
      (isPseudoCoherentFromOnAffinePair_of_isPseudoCoherentFrom f (hcoh j) U V hUV)
      n i hi hio)
  have h1 := h0.of_iso (P.mapDerivedCategory.mapIso
    ((Functor.mapDerivedCategorySingleFunctor R 0).app
      ((DerivedCategory.homologyFunctor X.Modules j).obj E)))
  have h2 := h1.of_iso ((Functor.mapDerivedCategorySingleFunctor P 0).app
    (R.obj ((DerivedCategory.homologyFunctor X.Modules j).obj E)))
  exact h2.of_iso ((DerivedCategory.singleFunctor _ 0).mapIso (ehom j).symm)

end Scheme.Hom

end AlgebraicGeometry

end
