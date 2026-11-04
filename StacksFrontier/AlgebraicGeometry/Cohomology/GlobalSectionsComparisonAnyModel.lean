module

public import StacksFrontier.AlgebraicGeometry.Cohomology.TildeTruncationTower

/-!
# The `Γ`-computes-`RΓ` comparison at an arbitrary model of the derived category

`AlgebraicGeometry.globalSectionsComplexComparison` is stated at free
`[HasDerivedCategory.{w₁} X.Modules]` and `[HasDerivedCategory.{w₂} (ModuleCat.{u} A)]` binders,
so it exists at every choice of model; but *invertibility* of it is proved, in
`StacksFrontier/AlgebraicGeometry/Cohomology/TildeTruncationTower.lean`, at the one model instance
search supplies, which is the locally small
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` of
`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean` together with
`ModuleCat.hasDerivedCategory`. `HasDerivedCategory` carries the localized category as data, so a
consumer which has pinned `CategoryTheory.HasDerivedCategory.standard` — as the files of
`StacksFrontier/AlgebraicGeometry/FormalGeometry/Completion/` do, the morphisms of their derived
categories living in `Type (u + 1)` — cannot apply that theorem: its statement is about a
different type. This file crosses the two.

## The crossing needs no comparison of the two models

The transport does not go through the comparison equivalence of
`StacksFrontier/Homology/DerivedCategory/ModelComparisonTransport.lean`. It does not have to:
`AlgebraicGeometry.isIso_globalSectionsComplexComparison_iff` — which is *already* stated at free
`HasDerivedCategory` binders — says that the comparison is invertible exactly when termwise
`A`-linear global sections carries one quasi-isomorphism `s : K ⟶ I` into a K-injective complex
to a quasi-isomorphism, and *that* condition mentions no derived category at all. So the two
models are compared through a condition which is the same for both, rather than through a functor
carrying one to the other.

What this buys over a transport along `Stacks.Injectives.grothendieckModelEquiv`: the statement
below holds for *any two* models with *any two* pairs of morphism universes, not only for the
standard and the shrunk one; it asks for no coherence between the two localization functors; and
it needs nothing of `Stacks.DerivedModel.rightDerivedModelIso`, which compares the two derived
global sections functors but says nothing about the comparison maps into them.

## Main results

* `AlgebraicGeometry.isIso_globalSectionsComplexComparison_iff_anyModel` — **the model
  crossing**: for a scheme `X` over `A`, a complex `K` of `𝒪_X`-modules and two choices of model
  for `D(𝒪_X)` and for `D(A)` each, the comparison `Q(Γ(X, K)) ⟶ RΓ(X, Q(K))` is invertible at
  one pair of models if and only if it is invertible at the other.
* `AlgebraicGeometry.isIso_globalSectionsComplexComparison_tilde_anyModel` — **unbounded affine
  vanishing at an arbitrary model**, the affine case of [Stacks, Tag 08D4]: for every cochain
  complex `M^\bullet` of `R`-modules and every choice of `D(𝒪_{Spec R})` and `D(R)`, the
  comparison `Q(\Gamma(\operatorname{Spec} R, \widetilde{M}^\bullet)) ⟶
  R\Gamma(Q(\widetilde{M}^\bullet))` is invertible.
* `AlgebraicGeometry.isIso_globalSectionsComplexComparison_tilde_standard` — the same at
  `CategoryTheory.HasDerivedCategory.standard`, which is the model its consumers in part (2) of
  [Stacks, Tag 0A0K] work at.

## Implementation notes

*Why the model arguments are explicit and not instance-implicit.* Both global instances of
`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean` are in the import closure of this file,
so a free `[HasDerivedCategory.{w} X.Modules]` binder here would give instance search two ways to
fill one argument of the statement — the warning recorded in the implementation notes of
`StacksFrontier/Homology/DerivedCategory/ModelComparisonTransport.lean`, and the reason every
declaration there names its models. The statements below name them too, which is why the
occurrences of `AlgebraicGeometry.globalSectionsComplexComparison` are written with `@`. At a use
site the models are determined by the goal, so they may be left as `_`.

No `@[stacks]` attribute appears below. Tag 08D4 is the statement for an arbitrary scheme and
what is proved here is the affine case already proved at one model in
`StacksFrontier/AlgebraicGeometry/Cohomology/TildeTruncationTower.lean`; this is that statement at
another model, not a second realization of the tag.

## References

* [Stacks Project, Tag 08D4](https://stacks.math.columbia.edu/tag/08D4)
* [Stacks Project, Tag 079Q](https://stacks.math.columbia.edu/tag/079Q)
* [Stacks Project, Tag 0A0K](https://stacks.math.columbia.edu/tag/0A0K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w₁ w₂ w₃ w₄ u

namespace AlgebraicGeometry

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-- **The `Γ`-computes-`RΓ` comparison is invertible at one model of the derived category if and
only if it is at any other.** Let `X` be a scheme over `A`, let `K` be a cochain complex of
`𝒪_X`-modules, and let `h₁, h₂` and `h₃, h₄` be two choices of model for `D(𝒪_X)` and `D(A)`,
with morphism universes `w₁, w₂` and `w₃, w₄` respectively. Then the comparison
`Q(Γ(X, K)) ⟶ RΓ(X, Q(K))` of `AlgebraicGeometry.globalSectionsComplexComparison` is invertible
at the first pair precisely when it is invertible at the second.

Both conditions are the same condition on no derived category at all. By
`AlgebraicGeometry.isIso_globalSectionsComplexComparison_iff`, invertibility at either pair of
models says that termwise `A`-linear global sections carries a quasi-isomorphism from `K` into a
K-injective complex to a quasi-isomorphism of complexes of `A`-modules; one such resolution,
supplied by `AlgebraicGeometry.Scheme.Modules.exists_quasiIso_isKInjective`, serves for both. -/
theorem isIso_globalSectionsComplexComparison_iff_anyModel
    (h₁ : HasDerivedCategory.{w₁} X.Modules) (h₂ : HasDerivedCategory.{w₂} (ModuleCat.{u} A))
    (h₃ : HasDerivedCategory.{w₃} X.Modules) (h₄ : HasDerivedCategory.{w₄} (ModuleCat.{u} A))
    (K : CochainComplex X.Modules ℤ) :
    IsIso (@globalSectionsComplexComparison _ _ _ f h₁ h₂ K) ↔
      IsIso (@globalSectionsComplexComparison _ _ _ f h₃ h₄ K) := by
  obtain ⟨I, s, hI, hs⟩ := Scheme.Modules.exists_quasiIso_isKInjective X K
  exact (@isIso_globalSectionsComplexComparison_iff _ _ _ f h₁ h₂ K I s hI hs).trans
    (@isIso_globalSectionsComplexComparison_iff _ _ _ f h₃ h₄ K I s hI hs).symm

/-- **Unbounded affine vanishing at an arbitrary model of the derived category**, the affine case
of [Stacks, Tag 08D4]. For every cochain complex `M^\bullet` of `R`-modules and every choice of
model for `D(𝒪_{Spec R})` and for `D(R)`, the comparison
`Q(\Gamma(\operatorname{Spec} R, \widetilde{M}^\bullet)) ⟶ R\Gamma(Q(\widetilde{M}^\bullet))` is
an isomorphism.

`AlgebraicGeometry.isIso_globalSectionsComplexComparison_tilde` proves this at the locally small
model, that being the one instance search supplies there, and
`AlgebraicGeometry.isIso_globalSectionsComplexComparison_iff_anyModel` carries it to the given
one. -/
theorem isIso_globalSectionsComplexComparison_tilde_anyModel (R : CommRingCat.{u})
    (h₁ : HasDerivedCategory.{w₁} (Spec R).Modules)
    (h₂ : HasDerivedCategory.{w₂} (ModuleCat.{u} R))
    (M : CochainComplex (ModuleCat.{u} R) ℤ) :
    IsIso (@globalSectionsComplexComparison _ _ _ (𝟙 (Spec R)) h₁ h₂
      (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)) :=
  (isIso_globalSectionsComplexComparison_iff_anyModel (𝟙 (Spec R)) _ _ h₁ h₂ _).1
    (isIso_globalSectionsComplexComparison_tilde R M)

/-- **Unbounded affine vanishing at the standard model of the derived category.**
`AlgebraicGeometry.isIso_globalSectionsComplexComparison_tilde_anyModel` at
`CategoryTheory.HasDerivedCategory.standard`, whose morphisms live in `Type (u + 1)`. This is the
model the part-(2) chain of [Stacks, Tag 0A0K] in
`StacksFrontier/AlgebraicGeometry/FormalGeometry/Completion/` pins with
`attribute [local instance] HasDerivedCategory.standard`, and at which the locally small
statement of `StacksFrontier/AlgebraicGeometry/Cohomology/TildeTruncationTower.lean` is not
applicable. -/
theorem isIso_globalSectionsComplexComparison_tilde_standard (R : CommRingCat.{u})
    (M : CochainComplex (ModuleCat.{u} R) ℤ) :
    IsIso (@globalSectionsComplexComparison _ _ _ (𝟙 (Spec R))
      (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)
      (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)) :=
  isIso_globalSectionsComplexComparison_tilde_anyModel R _ _ M

end AlgebraicGeometry

end
