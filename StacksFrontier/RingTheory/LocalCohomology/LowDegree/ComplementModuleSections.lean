module

public import StacksFrontier.RingTheory.LocalCohomology.LowDegree.LocalizationData

/-!
# The localization triangle compared with locally fractional sections on the complement

Let `I` be a finitely generated ideal of a commutative ring `A` and `U = Spec A \ V(I)`. The field
`Stacks.LocalCohomology.LocalizationTriangleData.sectionsIso` identifies the degree-zero cohomology
of the third term of the localization triangle with
`Stacks.LocalCohomology.complementGlobalSections`, the global sections on the scheme `U` of the
restriction of the sheaf associated to `M`. That is the shape the five-term exact sequence of
`StacksFrontier/RingTheory/LocalCohomology/LowDegree/ExactSequence.lean` consumes, because it has to
accept an arbitrary sheaf on `U` identified with that restriction.

This file gives the same comparison in the other standard shape:
`Stacks.LocalCohomology.moduleSections` of `M` on the open `U` of `Spec A` itself, with the
naturality and the formula `m ↦ m / 1` restated there. The two shapes differ by the transport
along `U.ι ''ᵁ ⊤ = U` of
`AlgebraicGeometry.Scheme.Opens.ι_image_top`, which is not an equality by definition, so the
restatement is not a matter of unfolding.

Together with `Stacks.LocalCohomology.isZero_homology_complement_of_neg` these are all the pieces
of the localization triangle in the locally fractional spelling, so no second structure is needed
to express it: a consumer that wants the whole package assembles it field by field out of a
`Stacks.LocalCohomology.LocalizationTriangleData` and the results below.

## Main definitions

* `Stacks.LocalCohomology.LocalizationTriangleData.moduleSectionsEquiv` —
  `H⁰(RΓ(U, M̃|U)) ≃ₗ[A] Γ(U, M̃)` with the sections taken on the open `U` of `Spec A`.

## Main results

* `Stacks.LocalCohomology.LocalizationTriangleData.moduleSectionsEquiv_naturality` — it is natural
  in the module.
* `Stacks.LocalCohomology.LocalizationTriangleData.moduleSectionsEquiv_restriction_eq` — the map
  induced by the second arrow of the triangle sends `m` to the section `m / 1`.
* `Stacks.LocalCohomology.exists_localizationTriangleData_isZero_homology_neg` — a finitely
  generated ideal has a localization triangle data whose third term has no negative cohomology.

## References

* [Stacks Project, Tag 0DWR](https://stacks.math.columbia.edu/tag/0DWR)
* [Stacks Project, Tag 0A6Q](https://stacks.math.columbia.edu/tag/0A6Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open AlgebraicGeometry TopologicalSpace

attribute [local instance] HasDerivedCategory.standard

universe v u

namespace Stacks.LocalCohomology

variable {A : Type u} [CommRing A] {I : Ideal A} {hI : I.FG}

/-- **`H⁰(RΓ(U, M̃|U)) ≃ₗ[A] Γ(U, M̃)`, with the sections taken on the open `U` of `Spec A`.**
The field `Stacks.LocalCohomology.LocalizationTriangleData.sectionsIso` states the same comparison
with the global sections of the restricted sheaf on the scheme `U`; the two are joined by
`Stacks.LocalCohomology.complementGlobalSectionsEquiv` and the transport along
`U.ι ''ᵁ ⊤ = U`. -/
def LocalizationTriangleData.moduleSectionsEquiv (D : LocalizationTriangleData.{u, v} A I hI)
    (M : ModuleCat.{v} A) :
    (DerivedCategory.homologyFunctor (ModuleCat.{v} A) 0).obj (D.complement.obj M) ≃ₗ[A]
      moduleSections M (complementZeroLocus A I) :=
  ((D.sectionsIso M).trans (complementGlobalSectionsEquiv I M).symm).trans
    (moduleSectionsCongr M (Scheme.Opens.ι_image_top (complementZeroLocus A I)))

/-- **The comparison of degree-zero cohomology with locally fractional sections on `U` is natural
in the module.** Both sides of the naturality square of
`Stacks.LocalCohomology.LocalizationTriangleData.sectionsIso_naturality` are functions on the
points of `U.ι ''ᵁ ⊤`, and `Stacks.LocalCohomology.associatedAbPresheafMap` acts on them
pointwise, so restricting that square along `U.ι ''ᵁ ⊤ = U` is enough. -/
theorem LocalizationTriangleData.moduleSectionsEquiv_naturality
    (D : LocalizationTriangleData.{u, v} A I hI) {M N : ModuleCat.{v} A} (f : M ⟶ N)
    (x : (DerivedCategory.homologyFunctor (ModuleCat.{v} A) 0).obj (D.complement.obj M)) :
    D.moduleSectionsEquiv N ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) 0).map
        (D.complement.map f) x) =
      (associatedAbPresheafMap f).app (op (complementZeroLocus A I))
        (D.moduleSectionsEquiv M x) := by
  refine Subtype.ext (funext fun y => ?_)
  exact congrFun (congrArg Subtype.val (D.sectionsIso_naturality f x)) _

/-- **The map induced by the second arrow of the localization triangle sends `m` to the section
`m / 1`**, in the locally fractional spelling on the open `U` of `Spec A`. -/
theorem LocalizationTriangleData.moduleSectionsEquiv_restriction_eq
    (D : LocalizationTriangleData.{u, v} A I hI) (M : ModuleCat.{v} A) (m : M) :
    D.moduleSectionsEquiv M ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) 0).map
      (D.restriction.app M)
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso
          (ModuleCat.{v} A) 0).inv.app M m)) =
      ⟨fun x ↦ LocalizedModule.mk m (1 : x.1.asIdeal.primeCompl),
        fun x ↦ ⟨_, x.2, 𝟙 _, m, 1, fun y ↦ ⟨by simp [Ideal.IsPrime.one_notMem], rfl⟩⟩⟩ := by
  refine Subtype.ext (funext fun y => ?_)
  exact congrFun (congrArg Subtype.val (D.restriction_eq M m)) _

variable (A I) in
/-- **A finitely generated ideal has an affine localization triangle data whose third term has no
negative cohomology.** The vanishing is not extra data: it is
`Stacks.LocalCohomology.isZero_homology_complement_of_neg`, a consequence of the other fields, so
it is recorded here as a property of the chosen data rather than as a field of
`Stacks.LocalCohomology.LocalizationTriangleData`. The module universe is independent of the ring
universe. -/
theorem exists_localizationTriangleData_isZero_homology_neg (hI : I.FG) :
    ∃ D : LocalizationTriangleData.{u, v} A I hI,
      ∀ (M : ModuleCat.{v} A) (i : ℤ), i < 0 →
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).obj
          (D.complement.obj M)) :=
  (nonempty_localizationTriangleData.{v} A I hI).elim fun D =>
    ⟨D, isZero_homology_complement_of_neg D⟩

end Stacks.LocalCohomology

end
