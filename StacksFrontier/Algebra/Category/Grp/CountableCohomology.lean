module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.CategoryTheory.Abelian.SerreClass.Basic

/-!
# Countable cohomology of a complex of abelian groups

The countable abelian groups form a Serre class: countability passes to subgroups and quotients,
and an extension of a countable group by a countable group is countable, because such an
extension is a quotient of a product of two countable groups. Consequently an object of the
derived category of abelian groups whose cohomology groups are countable in two of the three
vertices of a distinguished triangle has countable cohomology at the third, by the long exact
cohomology sequence.

## Main definitions

* `AddCommGrpCat.isCountable`: countability as an object property of abelian groups.
* `AddCommGrpCat.HasCountableCohomology`: every cohomology group of an object of `D(Ab)` is
  countable.

## Main results

* `AddCommGrpCat.instIsSerreClassIsCountable`: the countable abelian groups are a Serre class.
* `AddCommGrpCat.HasCountableCohomology.obj₁`, `.obj₂`, `.obj₃`: along a distinguished triangle,
  countable cohomology at two of the three vertices forces it at the third.
* `AddCommGrpCat.HasCountableCohomology.biprod`: stability under binary biproducts.

## Implementation notes

The three two-out-of-three results are the three exactness statements of the long exact
cohomology sequence of a distinguished triangle — `DerivedCategory.HomologySequence.exact₁`,
`exact₂` and `exact₃` — fed into `CategoryTheory.ObjectProperty.prop_X₂_of_exact`, which bounds
the middle term of an exact sequence by its outer terms for any Serre class. Only exactness at
one spot is used in each case, so no short exact sequence and no splitting is involved.

Stability under binary biproducts is deduced from `obj₂` applied to the split triangle
`X₁ ⟶ X₁ ⊞ X₂ ⟶ X₂ ⟶ X₁⟦1⟧`, which is distinguished in any pretriangulated category, rather
than from additivity of the cohomology functors.

The universe of the derived category is left free, so the statements apply both to the standard
model and to a locally small one.

## References

* [Stacks Project, Tag 0CRP](https://stacks.math.columbia.edu/tag/0CRP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w u

namespace AddCommGrpCat

/-- Countability of an abelian group, as an object property of the category of abelian
groups. -/
def isCountable : ObjectProperty AddCommGrpCat.{u} := fun M => Countable M

/-- An abelian group satisfies `isCountable` if and only if it is countable. -/
@[simp]
lemma prop_isCountable_iff (M : AddCommGrpCat.{u}) : isCountable M ↔ Countable M := Iff.rfl

/-- **The countable abelian groups form a Serre class**: they contain a zero object and are
closed under subobjects, quotients and extensions. -/
instance : isCountable.{u}.IsSerreClass where
  exists_zero := ⟨.of PUnit, isZero_of_subsingleton _,
    by rw [prop_isCountable_iff]; infer_instance⟩
  prop_of_mono {M N} f hf hN := by
    rw [AddCommGrpCat.mono_iff_injective] at hf
    simp only [prop_isCountable_iff] at hN ⊢
    exact Function.Injective.countable hf
  prop_of_epi {M N} f hf hM := by
    rw [AddCommGrpCat.epi_iff_surjective] at hf
    simp only [prop_isCountable_iff] at hM ⊢
    exact Function.Surjective.countable hf
  prop_X₂_of_shortExact {S} hS h₁ h₃ := by
    simp only [prop_isCountable_iff] at h₁ h₃ ⊢
    have hg := hS.epi_g
    rw [AddCommGrpCat.epi_iff_surjective] at hg
    obtain ⟨s, hs⟩ := hg.hasRightInverse
    have hφ : Function.Surjective (fun x : S.X₁ × S.X₃ => S.f x.1 + s x.2) := fun x₂ => by
      obtain ⟨x₁, hx₁⟩ := (ShortComplex.ab_exact_iff S).1 hS.exact (x₂ - s (S.g x₂))
        (by simp [hs (S.g x₂)])
      exact ⟨⟨x₁, S.g x₂⟩, by simp [hx₁]⟩
    exact Function.Surjective.countable hφ

variable [HasDerivedCategory.{w} AddCommGrpCat.{u}]

/-- An object of the derived category of abelian groups **has countable cohomology** when all of
its cohomology groups are countable. -/
def HasCountableCohomology (E : DerivedCategory AddCommGrpCat.{u}) : Prop :=
  ∀ i : ℤ, Countable ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).obj E)

/-- **Two out of three at the first vertex.** If the second and third vertices of a distinguished
triangle have countable cohomology, so does the first. -/
theorem HasCountableCohomology.obj₁ (T : Triangle (DerivedCategory AddCommGrpCat.{u}))
    (hT : T ∈ distTriang _) (h₂ : HasCountableCohomology T.obj₂)
    (h₃ : HasCountableCohomology T.obj₃) : HasCountableCohomology T.obj₁ := fun i =>
  isCountable.prop_X₂_of_exact
    (DerivedCategory.HomologySequence.exact₁ T hT (i - 1) i (by omega)) (h₃ (i - 1)) (h₂ i)

/-- **Two out of three at the second vertex.** If the first and third vertices of a distinguished
triangle have countable cohomology, so does the second. -/
theorem HasCountableCohomology.obj₂ (T : Triangle (DerivedCategory AddCommGrpCat.{u}))
    (hT : T ∈ distTriang _) (h₁ : HasCountableCohomology T.obj₁)
    (h₃ : HasCountableCohomology T.obj₃) : HasCountableCohomology T.obj₂ := fun i =>
  isCountable.prop_X₂_of_exact (DerivedCategory.HomologySequence.exact₂ T hT i) (h₁ i) (h₃ i)

/-- **Two out of three at the third vertex.** If the first and second vertices of a distinguished
triangle have countable cohomology, so does the third. -/
theorem HasCountableCohomology.obj₃ (T : Triangle (DerivedCategory AddCommGrpCat.{u}))
    (hT : T ∈ distTriang _) (h₁ : HasCountableCohomology T.obj₁)
    (h₂ : HasCountableCohomology T.obj₂) : HasCountableCohomology T.obj₃ := fun i =>
  isCountable.prop_X₂_of_exact
    (DerivedCategory.HomologySequence.exact₃ T hT i (i + 1) rfl) (h₂ i) (h₁ (i + 1))

/-- If `E` and `F` have countable cohomology, so does their biproduct `E ⊞ F`. -/
theorem HasCountableCohomology.biprod {E F : DerivedCategory AddCommGrpCat.{u}}
    (hE : HasCountableCohomology E) (hF : HasCountableCohomology F) :
    HasCountableCohomology (E ⊞ F) :=
  HasCountableCohomology.obj₂ (binaryBiproductTriangle E F)
    (binaryBiproductTriangle_distinguished E F) hE hF

end AddCommGrpCat

end
