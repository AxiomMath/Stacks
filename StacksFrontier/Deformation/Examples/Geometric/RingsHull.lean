module

public import StacksFrontier.Deformation.ClassicalCase
public import StacksFrontier.Deformation.Examples.Geometric.RingsInfinitesimalAutomorphisms
public import StacksFrontier.Deformation.Examples.Geometric.RingsTangentSpaceInjection
public import StacksFrontier.Deformation.Formal.VersalObject.IsomorphismClassesHull
public import StacksFrontier.Deformation.TangentSpace.LiftedComparison

/-!
# A hull for the deformations of a commutative algebra

Let `k` be a field, `P` a `k`-algebra and let the base `Λ` be classical. The deformations of
`P` form a deformation category, so its functor of fibrewise isomorphism classes satisfies
Schlessinger's conditions (S1) and (S2); if in addition its tangent space is finite
dimensional, the functor has a hull.

## Main results

All of them live in the namespace `Deformation.Examples`.

* `isPredeformationCategory_ringDeformationProjection`: the deformations of a `k`-algebra form
  a predeformation category.
* `schlessingerConditionS1_ringDeformationProjection` and
  `schlessingerConditionS2_ringDeformationProjection`: Schlessinger's conditions for it.
* `schlessingerConditionS2_isomorphismClasses_ringDeformation`: condition (S2) for the
  associated functor of isomorphism classes.
* `exists_hull_isomorphismClasses_ringDeformation`: the functor of isomorphism classes of
  deformations of `P` has a hull, given that its tangent space is finite dimensional.
* `finiteDimensional_artinianTangentSpace_ringDeformation`: the tangent-space clause of Stacks
  0DY4, for a `P` of finite type smooth outside a finite set of points.
* `exists_hull_isomorphismClasses_ringDeformation_of_finiteType`: the functor of isomorphism
  classes of deformations of a `P` of finite type smooth outside a finite set of points has a hull.

## References

* [Stacks Project, Tag 0ET4](https://stacks.math.columbia.edu/tag/0ET4)
* [Stacks Project, Tag 0DY4](https://stacks.math.columbia.edu/tag/0DY4)
-/

@[expose] public section

open CategoryTheory

namespace Deformation.Examples

universe u w

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable (P : Type w) [CommRing P] [Algebra k P]

/-- The deformations of a `k`-algebra form a predeformation category. -/
public theorem isPredeformationCategory_ringDeformationProjection :
    IsPredeformationCategory (ringDeformationProjection Λ k P) :=
  (ringDeformationCategory_isDeformationCategory (Λ := Λ) (k := k) P).predeformation

/-- **Stacks 06J7.** The deformations of a `k`-algebra satisfy Schlessinger's condition
(S1). -/
public theorem schlessingerConditionS1_ringDeformationProjection :
    SchlessingerConditionS1 (ringDeformationProjection Λ k P) :=
  schlessingerConditionS1_of_satisfiesRS
    (ringDeformationCategory_isDeformationCategory (Λ := Λ) (k := k) P).satisfiesRS

/-- **Stacks 06J7.** The deformations of a `k`-algebra satisfy Schlessinger's condition
(S2). -/
public theorem schlessingerConditionS2_ringDeformationProjection :
    SchlessingerConditionS2 (ringDeformationProjection Λ k P) :=
  schlessingerConditionS2_of_satisfiesRS
    (ringDeformationCategory_isDeformationCategory (Λ := Λ) (k := k) P).satisfiesRS

/-- **Stacks 06I0.** The functor of isomorphism classes of deformations of a `k`-algebra
satisfies Schlessinger's condition (S2). -/
public theorem schlessingerConditionS2_isomorphismClasses_ringDeformation :
    SchlessingerConditionS2 (Functor.Elements.π (Deformation.isomorphismClasses
      (BasedCategory.ofFunctor (ringDeformationProjection Λ k P))
      (isPredeformationCategory_ringDeformationProjection (Λ := Λ) (k := k) P).cofibered)) :=
  schlessingerConditionS2_of_isIsomorphismClasses _
    (isPredeformationCategory_ringDeformationProjection (Λ := Λ) (k := k) P).cofibered
    (schlessingerConditionS2_ringDeformationProjection (Λ := Λ) (k := k) P)
    (Or.inl (isPredeformationCategory_ringDeformationProjection (Λ := Λ) (k := k) P))

/-- The functor of isomorphism classes of deformations of a `k`-algebra `P` over a classical
base has a hull, provided its tangent space is finite dimensional: a versal formal object with
bijective differential. -/
public theorem exists_hull_isomorphismClasses_ringDeformation (hΛ : IsClassical Λ k)
    (hfinite :
      letI : Fact (IsPredeformationCategory.{u, w, w}
          (BasedCategory.ofFunctor (ringDeformationProjection Λ k P)).p) :=
        ⟨isPredeformationCategory_ringDeformationProjection (Λ := Λ) (k := k) P⟩
      letI : Fact (SchlessingerConditionS2 (Functor.Elements.π
          (Deformation.isomorphismClasses
            (BasedCategory.ofFunctor (ringDeformationProjection Λ k P))
            (isPredeformationCategory_ringDeformationProjection
              (Λ := Λ) (k := k) P).cofibered))) :=
        ⟨schlessingerConditionS2_isomorphismClasses_ringDeformation (Λ := Λ) (k := k) P⟩
      FiniteDimensional k (tangentSpaceArtinian.{u, w, w} Λ k (Deformation.isomorphismClasses
        (BasedCategory.ofFunctor (ringDeformationProjection Λ k P))
        (isPredeformationCategory_ringDeformationProjection (Λ := Λ) (k := k) P).cofibered))) :
    ∃ ξ : FormalObject (Functor.Elements.π (Deformation.isomorphismClasses
        (BasedCategory.ofFunctor (ringDeformationProjection Λ k P))
        (isPredeformationCategory_ringDeformationProjection (Λ := Λ) (k := k) P).cofibered)),
      IsVersal (categoryOfElements_projection_isCofibered (Deformation.isomorphismClasses
          (BasedCategory.ofFunctor (ringDeformationProjection Λ k P))
          (isPredeformationCategory_ringDeformationProjection
            (Λ := Λ) (k := k) P).cofibered)) ξ ∧
        HasBijectiveDifferential
          (categoryOfElements_projection_isCofibered (Deformation.isomorphismClasses
            (BasedCategory.ofFunctor (ringDeformationProjection Λ k P))
            (isPredeformationCategory_ringDeformationProjection
              (Λ := Λ) (k := k) P).cofibered))
          ξ := by
  let : IsNoetherianRing Λ := hΛ.isNoetherianRing
  let : Module.Finite Λ k := hΛ.moduleFinite
  let : Algebra.IsSeparable (residueImageField Λ k) k := hΛ.isSeparable
  let : Fact (IsPredeformationCategory.{u, w, w}
      (BasedCategory.ofFunctor (ringDeformationProjection Λ k P)).p) :=
    ⟨isPredeformationCategory_ringDeformationProjection (Λ := Λ) (k := k) P⟩
  let : Fact (SchlessingerConditionS2 (Functor.Elements.π (Deformation.isomorphismClasses
      (BasedCategory.ofFunctor (ringDeformationProjection Λ k P))
      (isPredeformationCategory_ringDeformationProjection (Λ := Λ) (k := k) P).cofibered))) :=
    ⟨schlessingerConditionS2_isomorphismClasses_ringDeformation (Λ := Λ) (k := k) P⟩
  let : FiniteDimensional k (tangentSpaceArtinian.{u, w, w} Λ k (Deformation.isomorphismClasses
      (BasedCategory.ofFunctor (ringDeformationProjection Λ k P))
      (isPredeformationCategory_ringDeformationProjection (Λ := Λ) (k := k) P).cofibered)) :=
    hfinite
  obtain ⟨ξ, -, hversal, hbijective⟩ :=
    exists_hull_isomorphismClasses.{u, w, w} Λ k
      (BasedCategory.ofFunctor (ringDeformationProjection Λ k P))
      (isPredeformationCategory_ringDeformationProjection (Λ := Λ) (k := k) P)
      (schlessingerConditionS1_ringDeformationProjection (Λ := Λ) (k := k) P)
      (schlessingerConditionS2_ringDeformationProjection (Λ := Λ) (k := k) P) inferInstance
  exact ⟨imageInIsomorphismClasses _
    (isPredeformationCategory_ringDeformationProjection (Λ := Λ) (k := k) P) ξ,
    hversal, hbijective⟩

attribute [local instance] HasDerivedCategory.standard

/-- **The tangent-space clause of Stacks 0DY4.** Let `k` be a field and `P` a `k`-algebra of
finite type which is smooth over `k` outside a finite set of primes. Then the tangent space of
the deformation category of `P`, in the model of Stacks 06IB with its canonical vector-space
structure of Stacks 06IH, is a finite-dimensional `k`-vector space. -/
public theorem finiteDimensional_artinianTangentSpace_ringDeformation
    [Algebra.FiniteType k P]
    (hsmooth : {q : PrimeSpectrum P | ¬ Algebra.IsSmoothAt k q.asIdeal}.Finite) :
    letI : Fact (IsPredeformationCategory.{u, w, w}
        (BasedCategory.ofFunctor (ringDeformationProjection Λ k P)).p) :=
      ⟨isPredeformationCategory_ringDeformationProjection (Λ := Λ) (k := k) P⟩
    letI : Fact (SchlessingerConditionS2 (Functor.Elements.π
        (Deformation.isomorphismClasses
          (BasedCategory.ofFunctor (ringDeformationProjection Λ k P))
          (isPredeformationCategory_ringDeformationProjection
            (Λ := Λ) (k := k) P).cofibered))) :=
      ⟨schlessingerConditionS2_isomorphismClasses_ringDeformation (Λ := Λ) (k := k) P⟩
    FiniteDimensional k (artinianTangentSpace Λ k (Deformation.isomorphismClasses
      (BasedCategory.ofFunctor (ringDeformationProjection Λ k P))
      (isPredeformationCategory_ringDeformationProjection (Λ := Λ) (k := k) P).cofibered)) := by
  have hfd : FiniteDimensional k
      ((naiveCotangentExtOneTensorFunctor k P).obj (FGModuleCat.of k k)) :=
    finiteDimensional_naiveCotangentExtOneTensorFunctor_obj_rankOne k P hsmooth
  exact Deformation.finiteDimensional_artinianTangentSpace_of_natural_injection
    (ringDeformationBasedCategory Λ k P)
    (isPredeformationCategory_ringDeformationProjection (Λ := Λ) (k := k) P)
    (schlessingerConditionS2_isomorphismClasses_ringDeformation (Λ := Λ) (k := k) P)
    (naiveCotangentExtOneTensorFunctor k P) (fun W ↦ tangentExtClass W)
    (fun f z ↦ tangentExtClass_naturality f z)
    (tangentExtClass_injective (Λ := Λ) (P := P) (FGModuleCat.of k k))

/-- Let `Λ → k` be a classical base, let `P` be a `k`-algebra of finite type, and suppose
`Spec(P) → Spec(k)` is smooth except at a finite number of points. Then the functor of fibrewise
isomorphism classes of deformations of `P` has a hull: a versal formal object with bijective
differential. -/
@[stacks 0ET4]
public theorem exists_hull_isomorphismClasses_ringDeformation_of_finiteType
    [Algebra.FiniteType k P]
    (hsmooth : {q : PrimeSpectrum P | ¬ Algebra.IsSmoothAt k q.asIdeal}.Finite)
    (hΛ : IsClassical Λ k) :
    ∃ ξ : FormalObject (Functor.Elements.π (Deformation.isomorphismClasses
        (BasedCategory.ofFunctor (ringDeformationProjection Λ k P))
        (isPredeformationCategory_ringDeformationProjection (Λ := Λ) (k := k) P).cofibered)),
      IsVersal (categoryOfElements_projection_isCofibered (Deformation.isomorphismClasses
          (BasedCategory.ofFunctor (ringDeformationProjection Λ k P))
          (isPredeformationCategory_ringDeformationProjection
            (Λ := Λ) (k := k) P).cofibered)) ξ ∧
        HasBijectiveDifferential
          (categoryOfElements_projection_isCofibered (Deformation.isomorphismClasses
            (BasedCategory.ofFunctor (ringDeformationProjection Λ k P))
            (isPredeformationCategory_ringDeformationProjection
              (Λ := Λ) (k := k) P).cofibered))
          ξ :=
  exists_hull_isomorphismClasses_ringDeformation P hΛ
    (Deformation.finiteDimensional_tangentSpaceArtinian_of_artinianTangentSpace
      (BasedCategory.ofFunctor (ringDeformationProjection Λ k P))
      (isPredeformationCategory_ringDeformationProjection (Λ := Λ) (k := k) P)
      (schlessingerConditionS2_isomorphismClasses_ringDeformation (Λ := Λ) (k := k) P)
      (finiteDimensional_artinianTangentSpace_ringDeformation P hsmooth))

end Deformation.Examples

end
