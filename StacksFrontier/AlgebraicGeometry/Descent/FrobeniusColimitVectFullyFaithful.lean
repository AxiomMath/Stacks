module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitRestrictIsColimit

/-!
# The comparison functor of Stacks Tag 0EXB is fully faithful

Let `p` be a prime and let `X` be a quasi-compact quasi-separated scheme in characteristic `p`.
Write `φ` for the `p`-th power endomorphism of `𝒪_X` and `colim_F 𝒪_X` for the colimit of the
sequential diagram of iterates of `φ`. This file records that **the comparison functor**

`colim_F Vect(X) ⥤ Vect(colim_F 𝒪_X)`

**of Stacks Tag 0EXB is fully faithful**, with no hypotheses beyond the ones the tag itself
carries.

Both halves are already proved in
`StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitFullyFaithful`, but there under the
explicit hypothesis that the cocone

`U_n (S_n 𝒢) = colim_j (U_φ)^{∘j}((S_φ)^{∘j}𝒢)`

is colimiting, which at the time was unproved. It is now
`AlgebraicGeometry.isColimit_frobeniusStageRestrictCocone`, and the only content of this file is
to feed it in.

## Main results

* `AlgebraicGeometry.faithful_frobeniusColimitVectComparison`: **the comparison functor of
  Stacks Tag 0EXB is faithful.**
* `AlgebraicGeometry.full_frobeniusColimitVectComparison`: **the comparison functor of Stacks
  Tag 0EXB is full.**
* `AlgebraicGeometry.isEquivalence_frobeniusColimitVectComparison_of_essSurj` and
  `AlgebraicGeometry.frobeniusColimitVectEquivalence_of_essSurj`: **the comparison functor is an
  equivalence, and Stacks Tag 0EXB holds as an equivalence of categories, as soon as every
  finite locally free `colim_F 𝒪_X`-module is isomorphic to the extension of scalars of a finite
  locally free `𝒪_X`-module along a coprojection.** That remaining hypothesis is essential
  surjectivity.

## Implementation notes

Essential surjectivity of the stage functors is carried here as a hypothesis rather than
discharged, in the shape `CategoryTheory.EndoColim.Pseudococone.essSurj_desc` consumes it; every
object of `colim_F Vect(X)` already lies in the image of a stage functor, so nothing else is
needed. It is proved in
`StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitVectEssSurj`, as
`AlgebraicGeometry.exists_frobeniusStageFunctor_obj_iso`, and the unconditional forms of the two
statements above are `AlgebraicGeometry.isEquivalence_frobeniusColimitVectComparison` and
`AlgebraicGeometry.frobeniusColimitVectEquivalence` there.

## References

* [Stacks Project, Tag 0EXA](https://stacks.math.columbia.edu/tag/0EXA)
* [Stacks Project, Tag 0EXB](https://stacks.math.columbia.edu/tag/0EXB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Frobenius TopologicalSpace

universe u

namespace AlgebraicGeometry

variable (X : Scheme.{u}) (p : ℕ) [Fact p.Prime] (hX : IsInCharacteristic X p)

/-- **The comparison functor of Stacks Tag 0EXB is faithful.** This is
`AlgebraicGeometry.faithful_frobeniusColimitVectComparison_of_isColimit` with its hypothesis
discharged by `AlgebraicGeometry.isColimit_frobeniusStageRestrictCocone`; no hypothesis beyond
those Stacks Tag 0EXB itself carries remains. -/
theorem faithful_frobeniusColimitVectComparison [CompactSpace X] [QuasiSeparatedSpace X] :
    (frobeniusColimitVectComparison X p hX).Faithful :=
  faithful_frobeniusColimitVectComparison_of_isColimit X p hX
    fun n G ↦ isColimit_frobeniusStageRestrictCocone X p hX G n

/-- **The comparison functor of Stacks Tag 0EXB is full.** This is
`AlgebraicGeometry.full_frobeniusColimitVectComparison_of_isColimit` with its hypothesis
discharged by `AlgebraicGeometry.isColimit_frobeniusStageRestrictCocone`; no hypothesis beyond
those Stacks Tag 0EXB itself carries remains. -/
theorem full_frobeniusColimitVectComparison [CompactSpace X] [QuasiSeparatedSpace X] :
    (frobeniusColimitVectComparison X p hX).Full :=
  full_frobeniusColimitVectComparison_of_isColimit X p hX
    fun n G ↦ isColimit_frobeniusStageRestrictCocone X p hX G n

/-- **The comparison functor of Stacks Tag 0EXB is an equivalence as soon as every finite locally
free `colim_F 𝒪_X`-module comes from a stage.** Full faithfulness is unconditional; the condition
left is exactly essential surjectivity of the stage functors, since every object of
`colim_F Vect(X)` lies in the image of one of them
(`CategoryTheory.EndoColim.Pseudococone.essSurj_desc`). -/
theorem isEquivalence_frobeniusColimitVectComparison_of_essSurj [CompactSpace X]
    [QuasiSeparatedSpace X]
    (hsurj : ∀ G : frobeniusColimitVectorBundles X p hX, ∃ (n : ℕ) (E : X.Vect),
      Nonempty ((frobeniusStageFunctor X p hX n).obj E ≅ G)) :
    (frobeniusColimitVectComparison X p hX).IsEquivalence :=
  have hf := faithful_frobeniusColimitVectComparison X p hX
  have hu := full_frobeniusColimitVectComparison X p hX
  { faithful := hf
    full := hu
    essSurj := (frobeniusColimitVectPseudococone X p hX).essSurj_desc hsurj }

/-- **The statement of Stacks Tag 0EXB, as an equivalence of categories, as soon as every finite
locally free `colim_F 𝒪_X`-module comes from a stage**: the category `colim_F Vect(X)` of Stacks
Tag 0EXA is equivalent to the category of finite locally free modules over the sheaf of rings
`colim_F 𝒪_X`, the equivalence being the comparison functor of the tag. The one hypothesis
beyond those the tag carries is essential surjectivity of the stage functors. -/
noncomputable def frobeniusColimitVectEquivalence_of_essSurj [CompactSpace X]
    [QuasiSeparatedSpace X]
    (hsurj : ∀ G : frobeniusColimitVectorBundles X p hX, ∃ (n : ℕ) (E : X.Vect),
      Nonempty ((frobeniusStageFunctor X p hX n).obj E ≅ G)) :
    frobeniusColimitVectModel X p hX ≌ frobeniusColimitVectorBundles X p hX :=
  have := isEquivalence_frobeniusColimitVectComparison_of_essSurj X p hX hsurj
  (frobeniusColimitVectComparison X p hX).asEquivalence

end AlgebraicGeometry

end
