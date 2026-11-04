module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.BoundedApproximation

/-!
# Moving a complex on an open of an open back to one open of `X`

Let `X` be a ringed space, `U` an open subspace and `V` an open subspace of `U`, and let `W` be
the image of `V` in `X`. The categories of modules on `(X|_U)|_V` and on `X|_W` are identified by
`AlgebraicGeometry.RingedSpace.nestedModulesEquivalence`, and its effect on restricted complexes
is `AlgebraicGeometry.RingedSpace.nestedComplexIso`. This file transports a complex along this
identification together with its strict perfection and with a quasi-isomorphism into a
restriction of a complex on `X`.

## Main definitions

* `AlgebraicGeometry.RingedSpace.nestedComplex`: the complex on `X|_W` corresponding to a
  complex on `(X|_U)|_V`.

## Main results

* `AlgebraicGeometry.RingedSpace.restrictModules_preservesHomology`: restriction to an open
  subspace preserves homology.
* `AlgebraicGeometry.RingedSpace.isStrictlyPerfect_nestedComplex`: the transport preserves
  strict perfection.
* `AlgebraicGeometry.RingedSpace.exists_quasiIso_nestedComplex` and
  `AlgebraicGeometry.RingedSpace.exists_quasiIso_nestedComplex_restrictComplex`: a
  quasi-isomorphism into the twice-restricted complex becomes a quasi-isomorphism into the
  restriction of the original complex to `W`.

## References

* [Stacks Project, Tag 08CB](https://stacks.math.columbia.edu/tag/08CB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect

namespace AlgebraicGeometry.RingedSpace

universe u

variable {X : RingedSpace.{u, u}}

attribute [local instance 10] nestedModulesEquivalence_functor_additive

/-- Restriction to an open subspace preserves homology. -/
theorem restrictModules_preservesHomology (X : RingedSpace.{u, u}) (U : Opens X.carrier) :
    (restrictModules.{u, u} X U).PreservesHomology := by
  have : PreservesFiniteLimits (restrictModules.{u, u} X U) :=
    restrictModules_preservesFiniteLimits X U
  have : PreservesFiniteColimits (restrictModules.{u, u} X U) :=
    restrictModules_preservesFiniteColimits X U
  have : (restrictModules.{u, u} X U).PreservesEpimorphisms :=
    preservesEpimorphisms_of_preservesColimitsOfShape _
  exact Functor.preservesHomology_of_preservesEpis_and_kernels _

/-- The complex of modules on the open subspace of `X` cut out by the image of `V`, obtained
from a complex of modules on `(X|_U)|_V` by the nested identification. -/
def nestedComplex (U : Opens X.carrier)
    (V : Opens (X.restrict U.isOpenEmbedding).carrier)
    (Q : CochainComplex
      (OXMod.{u, u} ((X.restrict U.isOpenEmbedding).restrict V.isOpenEmbedding)) ℤ) :
    CochainComplex
      (OXMod.{u, u} (X.restrict (U.isOpenEmbedding.functor.obj V).isOpenEmbedding)) ℤ :=
  ((nestedModulesEquivalence U V).functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q

/-- The terms of the transported complex are the images of the terms. -/
theorem nestedComplex_X (U : Opens X.carrier)
    (V : Opens (X.restrict U.isOpenEmbedding).carrier)
    (Q : CochainComplex
      (OXMod.{u, u} ((X.restrict U.isOpenEmbedding).restrict V.isOpenEmbedding)) ℤ) (j : ℤ) :
    (nestedComplex U V Q).X j = (nestedModulesEquivalence U V).functor.obj (Q.X j) :=
  rfl

/-- The nested identification preserves strict perfection. -/
theorem isStrictlyPerfect_nestedComplex (U : Opens X.carrier)
    (V : Opens (X.restrict U.isOpenEmbedding).carrier)
    {Q : CochainComplex
      (OXMod.{u, u} ((X.restrict U.isOpenEmbedding).restrict V.isOpenEmbedding)) ℤ}
    (hQ : IsStrictlyPerfect Q) : IsStrictlyPerfect (nestedComplex U V Q) :=
  isStrictlyPerfect_nestedModulesEquivalence U V Q hQ

/-- A quasi-isomorphism into the restriction to `V` of the restriction of `C` to `U` becomes,
under the nested identification, a quasi-isomorphism into the restriction of `C` to the open
subspace of `X` cut out by the image of `V`. -/
theorem exists_quasiIso_nestedComplex (U : Opens X.carrier)
    (V : Opens (X.restrict U.isOpenEmbedding).carrier)
    (C : CochainComplex (OXMod.{u, u} X) ℤ)
    {Q : CochainComplex
      (OXMod.{u, u} ((X.restrict U.isOpenEmbedding).restrict V.isOpenEmbedding)) ℤ}
    (β : Q ⟶ restrictComplex (restrictComplex C U) V) (hβ : QuasiIso β) :
    ∃ f : nestedComplex U V Q ⟶ restrictComplex C (U.isOpenEmbedding.functor.obj V),
      QuasiIso f := by
  have hEq : (nestedModulesEquivalence U V).functor.IsEquivalence :=
    (nestedModulesEquivalence U V).isEquivalence_functor
  have hPH : (nestedModulesEquivalence U V).functor.PreservesHomology := inferInstance
  have h₁ : QuasiIso (((nestedModulesEquivalence U V).functor.mapHomologicalComplex
      (ComplexShape.up ℤ)).map β) := inferInstance
  have h₂ : QuasiIso (nestedComplexIso U V C).hom := inferInstance
  exact ⟨((nestedModulesEquivalence U V).functor.mapHomologicalComplex
    (ComplexShape.up ℤ)).map β ≫ (nestedComplexIso U V C).hom,
    quasiIso_comp _ _ (hφ := h₁) (hφ' := h₂)⟩

/-- A quasi-isomorphism into the restriction of `C` to `U`, restricted to `V` and moved by the
nested identification, gives a quasi-isomorphism into the restriction of `C` to the open subspace
of `X` cut out by the image of `V`. -/
theorem exists_quasiIso_nestedComplex_restrictComplex (U : Opens X.carrier)
    (V : Opens (X.restrict U.isOpenEmbedding).carrier)
    (C : CochainComplex (OXMod.{u, u} X) ℤ)
    {P : CochainComplex (OXMod.{u, u} (X.restrict U.isOpenEmbedding)) ℤ}
    (g : P ⟶ restrictComplex C U) (hg : QuasiIso g) :
    ∃ f : nestedComplex U V (restrictComplex P V) ⟶
        restrictComplex C (U.isOpenEmbedding.functor.obj V), QuasiIso f := by
  have hPH : (restrictModules (X.restrict U.isOpenEmbedding) V).PreservesHomology :=
    restrictModules_preservesHomology _ V
  have h₁ : QuasiIso (((restrictModules (X.restrict U.isOpenEmbedding) V).mapHomologicalComplex
      (ComplexShape.up ℤ)).map g) := inferInstance
  exact exists_quasiIso_nestedComplex U V C
    (((restrictModules (X.restrict U.isOpenEmbedding) V).mapHomologicalComplex
      (ComplexShape.up ℤ)).map g) h₁

end AlgebraicGeometry.RingedSpace

end
