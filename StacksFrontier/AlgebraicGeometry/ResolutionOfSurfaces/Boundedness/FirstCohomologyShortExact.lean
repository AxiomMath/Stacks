module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.TorsionInFirstCohomology
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.GrauertRiemenschneider

/-!
# A short exact sequence of sheaves bounds the first cohomology of its sub

Let `X` be a scheme over `Spec A` and let `0 ⟶ ℱ ⟶ 𝒢 ⟶ 𝒞 ⟶ 0` be a short exact sequence of
sheaves of modules on `X`. The long exact sequence of the derived functors of `Γ(X, -)` opens

  `Γ(X, 𝒞) ⟶ H¹(X, ℱ) ⟶ H¹(X, 𝒢)`

so the image of the connecting map is a submodule `N` of `H¹(X, ℱ)` with `H¹(X, ℱ) ⧸ N`
embedded in `H¹(X, 𝒢)`, and `N` is annihilated by every element of `A` annihilating `Γ(X, 𝒞)`,
the connecting map being `A`-linear.

## Main results

* `AlgebraicGeometry.smul_globalSectionsAsBaseModule_eq_zero`: an element of the base ring
  annihilating a sheaf of modules annihilates its global sections.
* `AlgebraicGeometry.exists_submodule_firstCohomologySheaf_smul_eq_zero`: the submodule and the
  two properties above.

## Implementation notes

This is the cohomological step of the trace argument for surfaces ([Stacks, Tag 0AXL]). There
the sub is `π_*𝒪_Y` for a finite `π : Y ⟶ X`, the ambient is `𝒪_X^{⊕n}`, the map between them
is the pairing `Φ` against a basis of the fraction field extension through the trace, and the
element annihilating the cokernel is the determinant `d` of the pairing matrix — whose
ring-level form is `Stacks.Trace.det_pairingMatrix_smul_eq_zero`. The statement below is the
part of that step which does not mention the trace: it takes the sequence as given, and it is
stated for an arbitrary ambient sheaf rather than for a finite direct sum of copies of `𝒪_X`,
since the direct sum enters only in the computation of the bounding length.

The connecting map comes from the `δ`-functor
`Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives`, as in
`AlgebraicGeometry.exists_connecting_firstCohomology`, with `R⁰Γ(X, -)` identified with
`Γ(X, -)` by `CategoryTheory.Functor.toRightDerivedZero`. The submodule is produced existentially
rather than named, because the connecting map depends on a choice of resolution of the short
exact sequence.

The annihilation hypothesis is taken on the global sections of the cokernel rather than on the
cokernel itself, which is the weaker of the two and is what the proof uses;
`AlgebraicGeometry.smul_globalSectionsAsBaseModule_eq_zero` derives it from the sheaf-level
form, in which the cokernel is annihilated as a sheaf of modules.

## References

* [Stacks Project, Tag 0AXL](https://stacks.math.columbia.edu/tag/0AXL)
* [Stacks Project, Tag 0B4N](https://stacks.math.columbia.edu/tag/0B4N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

attribute [local instance] Scheme.commRingRingCatSheafObj HasDerivedCategory.standard

variable {A : Type u} [CommRing A] (X : Scheme.{u}) (f : X ⟶ Spec (.of A))

/-- An element of the base ring annihilating a sheaf of modules on `X` annihilates its global
sections. -/
theorem smul_globalSectionsAsBaseModule_eq_zero (d : A) (C : SheafOfModules.{u} X.ringCatSheaf)
    (hC : baseSmulModules X f d C = 0) (x : globalSectionsAsBaseModule X f C) :
    d • x = 0 := by
  have h : (Scheme.sectionsFunctor X).map (baseSmulModules X f d C)
      = baseSection X f d • 𝟙 ((Scheme.sectionsFunctor X).obj C) :=
    Scheme.sectionsFunctor_map_smulEnd X (baseSection X f d) C
  have hsmul : ((Scheme.sectionsFunctor X).map (baseSmulModules X f d C)).hom x = d • x := by
    rw [h]
    rfl
  rw [← hsmul, hC, Functor.map_zero]
  rfl

/-- **A short exact sequence `0 ⟶ ℱ ⟶ 𝒢 ⟶ 𝒞 ⟶ 0` of sheaves of modules on `X` bounds
`H¹(X, ℱ)` by `H¹(X, 𝒢)` modulo a submodule annihilated by anything annihilating `Γ(X, 𝒞)`.**

The submodule is the image of the connecting map `Γ(X, 𝒞) ⟶ H¹(X, ℱ)` of the long exact
sequence; the quotient by it is the image of `H¹(X, ℱ) ⟶ H¹(X, 𝒢)`, and the connecting map is
`A`-linear, so `d` annihilates its image as soon as it annihilates `Γ(X, 𝒞)`.

This is the exact sequence `H⁰(X, Coker Φ) ⟶ H¹(Y, 𝒪_Y) ⟶ H¹(X, 𝒪_X)^{⊕n}` of the proof of
[Stacks, Tag 0AXL] with the trace pairing `Φ` abstracted away. -/
theorem exists_submodule_firstCohomologySheaf_smul_eq_zero (d : A)
    {F G C : SheafOfModules.{u} X.ringCatSheaf} (Φ : F ⟶ G) (p : G ⟶ C) (hz : Φ ≫ p = 0)
    (hS : (ShortComplex.mk Φ p hz).ShortExact)
    (hd : ∀ x : globalSectionsAsBaseModule X f C, d • x = 0) :
    ∃ N : Submodule A (firstCohomologySheafAsBaseModule X f F),
      (∀ x ∈ N, d • x = 0) ∧
        Module.length A (firstCohomologySheafAsBaseModule X f F ⧸ N) ≤
          Module.length A (firstCohomologySheafAsBaseModule X f G) := by
  let D := Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
    (Scheme.sectionsFunctor X)
  let δ' : ((Scheme.sectionsFunctor X).rightDerived 0).obj C ⟶
      ((Scheme.sectionsFunctor X).rightDerived 1).obj F := D.δ hS 0
  let u : Scheme.sectionsFunctor X ⟶ (Scheme.sectionsFunctor X).rightDerived 0 :=
    (Scheme.sectionsFunctor X).toRightDerivedZero
  let δ : globalSectionsAsBaseModule X f C →ₗ[A] firstCohomologySheafAsBaseModule X f F :=
    ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).map
      (u.app C ≫ δ')).hom
  let φ : firstCohomologySheafAsBaseModule X f F →ₗ[A] firstCohomologySheafAsBaseModule X f G :=
    ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).map
      (((Scheme.sectionsFunctor X).rightDerived 1).map Φ)).hom
  have e2 : LinearMap.range δ'.hom
      = LinearMap.ker (((Scheme.sectionsFunctor X).rightDerived 1).map Φ).hom :=
    (ShortComplex.moduleCat_exact_iff_range_eq_ker _).1 (D.exact_δ₂ hS 0)
  have hker : LinearMap.range δ = LinearMap.ker φ := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact (SetLike.ext_iff.mp e2 _).1 ⟨(u.app C).hom x, rfl⟩
    · intro hy
      obtain ⟨w, rfl⟩ := (SetLike.ext_iff.mp e2 y).2 hy
      obtain ⟨x, rfl⟩ := (ConcreteCategory.bijective_of_isIso (u.app C)).2 w
      exact ⟨x, rfl⟩
  refine ⟨LinearMap.range δ, ?_, ?_⟩
  · rintro x ⟨y, rfl⟩
    rw [← map_smul, hd y, map_zero]
  · rw [hker, φ.quotKerEquivRange.length_eq]
    exact Module.length_le_of_injective _ (Submodule.injective_subtype _)

end AlgebraicGeometry

end
