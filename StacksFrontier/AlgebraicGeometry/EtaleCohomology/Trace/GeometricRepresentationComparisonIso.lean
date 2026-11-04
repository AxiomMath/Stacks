module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricRepresentationEffaceable

/-!
# `H^i(π₁(X_{k̄}), M) ≅ H^i(X_{k̄}, ℱ_M)`

Let `X` be a quasi-compact quasi-separated connected curve over `k`, `K` an algebraic closure of
`k` with `X_K` connected, and `Λ` a finite ring with `#Λ` invertible in `K`. If `X_K` is affine,
or a smooth proper curve of genus `≥ 1`, then both `M ↦ H^i(π₁(X_K), M)` and
`M ↦ H^i(X_K, ℱ_M)` are universal δ-functors on finite `Λ`-modules with continuous
`π₁(X)`-action, which agree in degree zero (Tag 03VL); hence the comparison morphism
`AlgebraicGeometry.geometricComparison` is an isomorphism of δ-functors (Tag 03VM, cohomological
half: "both sides are universal δ-functors").

## Main results

* `AlgebraicGeometry.isUniversal_geometricRepresentationCohomology_of_genus`,
  `AlgebraicGeometry.isUniversal_geometricRepresentationCohomology_of_isAffine` — the étale side is
  universal.
* `AlgebraicGeometry.geometricComparisonIsoOfGenus`,
  `AlgebraicGeometry.geometricComparisonIsoOfIsAffine` — the isomorphism of δ-functors, whose
  underlying morphism is `geometricComparison`.
* `AlgebraicGeometry.bijective_geometricComparison_app_of_genus`,
  `AlgebraicGeometry.bijective_geometricComparison_app_of_isAffine` — bijectivity in every degree.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.GroupCohomology Stacks.ContinuousCohomology

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (Λ : Type) [Ring Λ]
  [Finite Λ] {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k)) (K : Type u) [Field K]
  [Algebra k K] (hK : B.Contains (Stacks.Frobenius.fieldBaseChange (Over.mk f) K))
  [ConnectedSpace (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)]
  (y : GeometricPoint (Stacks.Frobenius.fieldBaseChange (Over.mk f) K))
  [IsAlgClosure k K] [CompactSpace X.1] [QuasiSeparatedSpace X.1]

omit [ConnectedSpace X.1] [Finite Λ]
  [ConnectedSpace (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)]
  [IsAlgClosure k K] [CompactSpace X.1] [QuasiSeparatedSpace X.1] in
/-- The components of an isomorphism of δ-functors with values in modules are bijective. -/
theorem bijective_app_of_iso {A : Type*} [Category A] [Abelian A]
    {F G : DeltaFunctor A (ModuleCat.{u + 1} Λ)} (α : F ≅ G) (n : ℕ) (M : A) :
    Function.Bijective ((α.hom.app n).app M) := by
  have h1 : (α.hom.app n).app M ≫ (α.inv.app n).app M = 𝟙 _ :=
    congrArg (fun η => (η.app n).app M) α.hom_inv_id
  have h2 : (α.inv.app n).app M ≫ (α.hom.app n).app M = 𝟙 _ :=
    congrArg (fun η => (η.app n).app M) α.inv_hom_id
  have : IsIso ((α.hom.app n).app M) := ⟨⟨_, h1, h2⟩⟩
  exact ConcreteCategory.bijective_of_isIso _

section Genus

variable (hcurve : IsCurve k f)
  [IsCurve K (pullback.snd (Over.mk f).hom (Stacks.Frobenius.specAlgebraMap k K))]
  [Smooth (pullback.snd (Over.mk f).hom (Stacks.Frobenius.specAlgebraMap k K))]
  [IsProper (pullback.snd (Over.mk f).hom (Stacks.Frobenius.specAlgebraMap k K))]
  (hg : 1 ≤ genus (pullback.snd (Over.mk f).hom (Stacks.Frobenius.specAlgebraMap k K)))
  (hΛ : IsUnit ((Nat.card Λ : ℕ) : K))

include hcurve hg hΛ

/-- **`ρ ↦ H^i(X_K, ℱ_ρ)` is a universal δ-functor** for `X_K` smooth proper of genus `≥ 1`. -/
theorem isUniversal_geometricRepresentationCohomology_of_genus :
    (geometricRepresentationCohomology.{u, 0} B X (y.map (fieldBaseChangeObjProj B X f K hK).hom)
      Λ f K).IsUniversal :=
  have := elementwiseEffaceable_geometricRepresentationCohomology_of_genus B X
    (y.map (fieldBaseChangeObjProj B X f K hK).hom) Λ f K hcurve hK hg hΛ
  DeltaFunctor.isUniversal_of_elementwiseEffaceable _

/-- **`H^i(π₁(X_K), M) ≅ H^i(X_K, ℱ_M)` as δ-functors**, for `X_K` smooth proper of genus `≥ 1`:
the isomorphism of universal δ-functors extending the degree-zero identification. -/
def geometricComparisonIsoOfGenus :
    geometricGroupCohomology B X Λ f K hK y ≅
      geometricRepresentationCohomology.{u, 0} B X (y.map (fieldBaseChangeObjProj B X f K hK).hom)
        Λ f K :=
  haveI := isUniversal_geometricGroupCohomology B X Λ f K hK y
  haveI := isUniversal_geometricRepresentationCohomology_of_genus B X Λ f K hK y hcurve hg hΛ
  DeltaFunctor.IsUniversal.isoOfIso (geometricComparisonZero B X Λ f K hK y)

/-- The isomorphism `AlgebraicGeometry.geometricComparisonIsoOfGenus` is the comparison
morphism. -/
theorem geometricComparisonIsoOfGenus_hom :
    (geometricComparisonIsoOfGenus B X Λ f K hK y hcurve hg hΛ).hom =
      geometricComparison B X Λ f K hK y :=
  rfl

/-- **`H^n(π₁(X_K), M) ≅ H^n(X_K, ℱ_M)` through the comparison morphism, in every degree**, for
`X_K` smooth proper of genus `≥ 1`. -/
theorem bijective_geometricComparison_app_of_genus (n : ℕ)
    (M : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f K hK).hom))) :
    Function.Bijective (((geometricComparison B X Λ f K hK y).app n).app M) := by
  rw [← geometricComparisonIsoOfGenus_hom B X Λ f K hK y hcurve hg hΛ]
  exact bijective_app_of_iso Λ (geometricComparisonIsoOfGenus B X Λ f K hK y hcurve hg hΛ) n M

end Genus

section Affine

variable (hcurve : IsCurve k f) [IsAffine (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)]

include hcurve

/-- **`ρ ↦ H^i(X_K, ℱ_ρ)` is a universal δ-functor** for `X_K` affine. -/
theorem isUniversal_geometricRepresentationCohomology_of_isAffine :
    (geometricRepresentationCohomology.{u, 0} B X (y.map (fieldBaseChangeObjProj B X f K hK).hom)
      Λ f K).IsUniversal :=
  have : Algebra.IsAlgebraic k K := IsAlgClosure.isAlgebraic
  have : IsAlgClosed K := IsAlgClosure.isAlgClosed k
  have := elementwiseEffaceable_geometricRepresentationCohomology_of_isAffine B X
    (y.map (fieldBaseChangeObjProj B X f K hK).hom) Λ f K hcurve
  DeltaFunctor.isUniversal_of_elementwiseEffaceable _

/-- **`H^i(π₁(X_K), M) ≅ H^i(X_K, ℱ_M)` as δ-functors**, for `X_K` affine. -/
def geometricComparisonIsoOfIsAffine :
    geometricGroupCohomology B X Λ f K hK y ≅
      geometricRepresentationCohomology.{u, 0} B X (y.map (fieldBaseChangeObjProj B X f K hK).hom)
        Λ f K :=
  haveI := isUniversal_geometricGroupCohomology B X Λ f K hK y
  haveI := isUniversal_geometricRepresentationCohomology_of_isAffine B X Λ f K hK y hcurve
  DeltaFunctor.IsUniversal.isoOfIso (geometricComparisonZero B X Λ f K hK y)

/-- The isomorphism `AlgebraicGeometry.geometricComparisonIsoOfIsAffine` is the comparison
morphism. -/
theorem geometricComparisonIsoOfIsAffine_hom :
    (geometricComparisonIsoOfIsAffine B X Λ f K hK y hcurve).hom =
      geometricComparison B X Λ f K hK y :=
  rfl

/-- **`H^n(π₁(X_K), M) ≅ H^n(X_K, ℱ_M)` through the comparison morphism, in every degree**, for
`X_K` affine. -/
theorem bijective_geometricComparison_app_of_isAffine (n : ℕ)
    (M : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f K hK).hom))) :
    Function.Bijective (((geometricComparison B X Λ f K hK y).app n).app M) := by
  rw [← geometricComparisonIsoOfIsAffine_hom B X Λ f K hK y hcurve]
  exact bijective_app_of_iso Λ (geometricComparisonIsoOfIsAffine B X Λ f K hK y hcurve) n M

end Affine

end AlgebraicGeometry

end
