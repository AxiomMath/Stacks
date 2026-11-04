module

public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import StacksFrontier.Algebra.Homology.DerivedCategory.AcyclicObjects
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.Homology.DerivedIndexing.Extend
public import StacksFrontier.Topology.Sheaves.Cohomology.Leray.AbelianSheafSpectralSequence

/-!
# An additive functor carries a quasi-isomorphism of acyclic complexes to a quasi-isomorphism

Let `T : 𝒟 ⥤ ℰ` be an additive, left exact functor between abelian categories, with `𝒟` having
enough injectives. Let `φ : K ⟶ L` be a quasi-isomorphism of `ℕ`-indexed cochain complexes of
`𝒟` all of whose terms are right acyclic for `T` ([Stacks, Tag 0157]). Then `T` applied
termwise to `φ` is again a quasi-isomorphism.

This is the input that replaces "`T` preserves injective objects" when one wants to read the
right derived functors of `T` on a resolution by `T`-acyclic objects rather than by injective
objects. The two engines are already in the repository and this file only joins them:
`CategoryTheory.Functor.RightAcyclicCriterion.map_quasiIso` is the statement for `ℤ`-indexed
complexes, and `CategoryTheory.Functor.rightAcyclic_and_shortExact_map_of_shortExact`
([Stacks, Tag 015D]) is the two-out-of-three property of right acyclicity which that engine
asks for as a hypothesis.

## Main results

* `Stacks.AcyclicQuasiIso.rightAcyclic_of_iso` and
  `Stacks.AcyclicQuasiIso.rightAcyclic_extend_X`: right acyclicity is invariant under
  isomorphism, and the extension by zero of a complex of right acyclic objects has right
  acyclic terms in every integer degree.
* `Stacks.AcyclicQuasiIso.quasiIso_map`: `T` applied termwise to a quasi-isomorphism between
  complexes of `T`-acyclic objects is a quasi-isomorphism.
* `Stacks.AcyclicQuasiIso.isIso_homologyMap_map`: hence it is invertible on homology in every
  degree, which is the form the comparison of resolutions uses.

## Implementation notes

The `ℕ`-indexed statement is obtained from the `ℤ`-indexed one by extension by zero along
`ComplexShape.embeddingUpNat`, in three steps, each of which is a lemma that already exists:
`HomologicalComplex.quasiIso_extendMap_iff` transports the hypothesis up and the conclusion
down, and `Stacks.DerivedIndexing.mapExtendNatIso` says that extension by zero commutes with
`T` applied termwise, so that the complex the engine is run on is the extension of the complex
the conclusion is about.

The degrees of the extension that `ComplexShape.embeddingUpNat` does not hit carry a zero
object, and a zero object is injective, hence right acyclic for every additive functor by
`Stacks.Cohomology.Leray.rightAcyclic_of_injective`; this is why `rightAcyclic_extend_X` needs no
closure property of the acyclic objects under sums or zeros.

Right acyclicity is read through part (2) of [Stacks, Tag 015C]
(`CategoryTheory.Functor.rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus`) whenever it has
to be transported, which is why left exactness of `T` is assumed throughout: part (2) is the
half that repackages a vanishing statement as acyclicity.

## References

* [Stacks Project, Tag 0157](https://stacks.math.columbia.edu/tag/0157)
* [Stacks Project, Tag 015C](https://stacks.math.columbia.edu/tag/015C)
* [Stacks Project, Tag 015D](https://stacks.math.columbia.edu/tag/015D)
* [Stacks Project, Tag 05T8](https://stacks.math.columbia.edu/tag/05T8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace Stacks.AcyclicQuasiIso

universe v v' u u'

-- As in `StacksFrontier.AlgebraicGeometry.LeraySectionsCollapse.Basic`: instance search for
-- `HasRightDerivedFunctor`, which `Functor.rightAcyclic` mentions, would otherwise try to
-- prove termwise injectivity of an unknown complex, so the cheap instance coming from
-- `EnoughInjectives` is given precedence.
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {D : Type u} {E : Type u'} [Category.{v} D] [Category.{v'} E] [Abelian D] [Abelian E]
  [HasDerivedCategory.{max u v} D] [HasDerivedCategory.{max u' v'} E] [EnoughInjectives D]
  (T : D ⥤ E) [T.Additive] [PreservesFiniteLimits T]

/-- Right acyclicity, as the vanishing of the higher right derived functors: part (2) of
[Stacks, Tag 015C] for a left exact functor. -/
theorem rightAcyclic_iff_isZero (A : D) :
    T.rightAcyclic A ↔ ∀ i > 0, IsZero ((T.rightDerivedPlus i).obj A) :=
  (Functor.rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus T A).2 inferInstance

/-- Right acyclicity is invariant under isomorphism. -/
theorem rightAcyclic_of_iso {A B : D} (e : A ≅ B) (hA : T.rightAcyclic A) :
    T.rightAcyclic B :=
  (rightAcyclic_iff_isZero T B).2 fun i hi =>
    ((rightAcyclic_iff_isZero T A).1 hA i hi).of_iso ((T.rightDerivedPlus i).mapIso e).symm

omit [PreservesFiniteLimits T] in
/-- Every object of `𝒟` admits a monomorphism into a right acyclic one: the injective hull
will do, by `Stacks.Cohomology.Leray.rightAcyclic_of_injective`. -/
theorem exists_mono_rightAcyclic (A : D) :
    ∃ (B : D) (_ : T.rightAcyclic B) (i : A ⟶ B), Mono i :=
  ⟨Injective.under A,
    Stacks.Cohomology.Leray.rightAcyclic_of_injective T _ (Injective.injective_under A),
    Injective.ι A, inferInstance⟩

/-- The two-out-of-three property of right acyclicity, in the form the criterion of
[Stacks, Tag 05T8] asks for: in a short exact sequence whose first two terms are right acyclic,
the third is right acyclic and the sequence stays short exact under `T`. -/
theorem rightAcyclic_shortExact (S : ShortComplex D) (hS : S.ShortExact)
    (h₁ : T.rightAcyclic S.X₁) (h₂ : T.rightAcyclic S.X₂) :
    T.rightAcyclic S.X₃ ∧ (S.map T).ShortExact :=
  (Functor.rightAcyclic_and_shortExact_map_of_shortExact T S hS).2.1 h₁ h₂

/-- The extension by zero of a complex of right acyclic objects has right acyclic terms in
every integer degree: the degrees in the image of the embedding carry a term of the original
complex, and the others carry a zero object, which is injective. -/
theorem rightAcyclic_extend_X (K : CochainComplex D ℕ)
    (hK : ∀ n, T.rightAcyclic (K.X n)) (m : ℤ) :
    T.rightAcyclic ((K.extend ComplexShape.embeddingUpNat).X m) := by
  by_cases! hm : ∃ k : ℕ, ComplexShape.embeddingUpNat.f k = m
  · obtain ⟨k, hk⟩ := hm
    exact rightAcyclic_of_iso T (K.extendXIso ComplexShape.embeddingUpNat hk).symm (hK k)
  · exact Stacks.Cohomology.Leray.rightAcyclic_of_injective T _
      (K.isZero_extend_X ComplexShape.embeddingUpNat m (fun k => hm k)).injective

/-- **An additive left exact functor carries a quasi-isomorphism between complexes of acyclic
objects to a quasi-isomorphism.** -/
theorem quasiIso_map {K L : CochainComplex D ℕ} (φ : K ⟶ L) [QuasiIso φ]
    (hK : ∀ n, T.rightAcyclic (K.X n)) (hL : ∀ n, T.rightAcyclic (L.X n)) :
    QuasiIso ((T.mapHomologicalComplex (ComplexShape.up ℕ)).map φ) := by
  have : QuasiIso ((ComplexShape.embeddingUpNat.extendFunctor D).map φ) :=
    inferInstanceAs (QuasiIso (HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat))
  have key : QuasiIso ((ComplexShape.embeddingUpNat.extendFunctor E).map
      ((T.mapHomologicalComplex (ComplexShape.up ℕ)).map φ)) := by
    have hz : QuasiIso ((T.mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((ComplexShape.embeddingUpNat.extendFunctor D).map φ)) :=
      Functor.RightAcyclicCriterion.map_quasiIso T T.rightAcyclic
        (exists_mono_rightAcyclic T) (fun S hS h₁ h₂ => rightAcyclic_shortExact T S hS h₁ h₂) _
        ⟨0, inferInstanceAs (CochainComplex.IsStrictlyGE
          (K.extend ComplexShape.embeddingUpNat) 0)⟩
        ⟨0, inferInstanceAs (CochainComplex.IsStrictlyGE
          (L.extend ComplexShape.embeddingUpNat) 0)⟩
        (rightAcyclic_extend_X T K hK) (rightAcyclic_extend_X T L hL)
    have e := Stacks.DerivedIndexing.mapExtendNatIso T
      (c' := ComplexShape.up ℤ) ComplexShape.embeddingUpNat
    have hnat := e.hom.naturality φ
    simp only [Functor.comp_map] at hnat
    have hcomp : QuasiIso (e.hom.app K ≫ (T.mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((ComplexShape.embeddingUpNat.extendFunctor D).map φ)) := quasiIso_comp _ _
    rw [← hnat] at hcomp
    exact quasiIso_of_comp_right _ (e.hom.app L)
  have key' : QuasiIso (HomologicalComplex.extendMap
      ((T.mapHomologicalComplex (ComplexShape.up ℕ)).map φ) ComplexShape.embeddingUpNat) := key
  rwa [HomologicalComplex.quasiIso_extendMap_iff] at key'

/-- The homology comparison the collapse of a composite is computed with: `T` applied termwise
to a quasi-isomorphism between complexes of `T`-acyclic objects is invertible on homology in
every degree. -/
theorem isIso_homologyMap_map {K L : CochainComplex D ℕ} (φ : K ⟶ L) [QuasiIso φ]
    (hK : ∀ n, T.rightAcyclic (K.X n)) (hL : ∀ n, T.rightAcyclic (L.X n)) (n : ℕ) :
    IsIso (homologyMap ((T.mapHomologicalComplex (ComplexShape.up ℕ)).map φ) n) := by
  have := quasiIso_map T φ hK hL
  rw [← quasiIsoAt_iff_isIso_homologyMap]
  infer_instance

end Stacks.AcyclicQuasiIso

end
