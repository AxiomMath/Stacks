module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorSingleRightDerived
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.DerivedGlobalSections
public import StacksFrontier.AlgebraicGeometry.Modules.GlobalSectionsOverGamma
public import StacksFrontier.Topology.Sheaves.Cohomology.CechToCohomology.AcyclicCovering
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.UniformBoundSpellingBridge
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.CohomologyAdicCompletionMittagLeffler
public import StacksFrontier.CategoryTheory.Abelian.InverseSystem

/-!
# The two models of the cohomology of a scheme over its base ring

The cohomology `Hᵖ(X, ℱ)` of a sheaf of modules on a scheme over `Spec A` is written in this
library in two unrelated ways, and the chain that proves the properness clause of
[Stacks, Tag 0A0M] crosses from one to the other.

* `(AlgebraicGeometry.moduleGlobalSections X).rightDerived p` is Mathlib's `ℕ`-indexed right
  derived functor of `Γ(X, −)` computed by the chosen injective resolution, valued in
  `Γ(X, 𝒪_X)`-modules. This is the model [Stacks, Tag 02OB] is stated in: the Mittag-Leffler
  clause of `Stacks.Cohomology.FormalFunctions.exists_uniform_bound_cohomology_idealPowerQuotient`
  is about the tower `Stacks.Algebraization.adicQuotientSystem 𝓘 ℱ ⋙ … .rightDerived p`.
* `DerivedCategory.singleFunctor X.Modules 0 ⋙ AlgebraicGeometry.derivedGlobalSectionsOver f ⋙
  DerivedCategory.homologyFunctor (ModuleCat A) p` is the cohomology of `RΓ(X, ℱ)` taken in the
  *unbounded* derived category of `A`-modules. This is the model [Stacks, Tag 0A0M] is stated in:
  the sequence of `Stacks.Algebraization.exists_shortExact_cohomology_limit_adicQuotients` and the
  hypothesis `hML` of
  `Stacks.Algebraization.exists_iso_cohomology_limit_adicQuotients_of_isMittagLeffler` both use
  it.

This file relates them. Restriction of scalars along `baseRingHom` turns the first into the
second, naturally in the sheaf of modules, so the Mittag-Leffler condition transports: restriction
of scalars is exact, which is what `IsMittagLefflerCategorical.map` consumes, and the comparison
is a natural isomorphism of towers, which is what `IsMittagLefflerCategorical.of_natIso` consumes.

With that in place the two steps compose, and the conclusion the properness clause of
[Stacks, Tag 0A0M] draws — that the `R¹lim` term vanishes, so that

`Hᵖ(X, lim ℱ/𝓘ⁿℱ) ≅ lim Hᵖ(X, ℱ/𝓘ⁿℱ)` —

holds granted [Stacks, Tag 02O8] alone, in the general form
`Stacks.Cohomology.FormalFunctions.exists_uniform_bound_idealPowerQuotient_of_reesFinite`
consumes it.

## Main definitions

* `Stacks.Algebraization.rightDerivedRestrictScalarsIso` — `Rᵖ Γ(X, −) ⊗ A` is `Hᵖ(RΓ(X, −))`:
  the `ℕ`-indexed right derived functor of global sections, restricted to the base ring, is the
  degree-`p` cohomology of unbounded derived global sections of the sheaf placed in degree zero.
* `Stacks.Algebraization.adicQuotientRightDerivedRestrictScalarsIso` — the same comparison
  whiskered with the adic tower, at the shape the hypothesis `hML` is stated in.

## Main results

* `Stacks.Algebraization.isMittagLefflerCategorical_homologyDerivedGlobalSections` — the
  Mittag-Leffler condition for the tower `n ↦ Hᵖ(X, ℱ/𝓘ⁿℱ)` in the
  `(moduleGlobalSections X).rightDerived p` model implies it in the unbounded model.
* `Stacks.Algebraization.exists_iso_cohomology_limit_adicQuotients_of_reesFinite` — the
  properness conclusion of [Stacks, Tag 0A0M] granted [Stacks, Tag 02O8].

## Implementation notes

The comparison is two already available steps and an identity. The identity is
`AlgebraicGeometry.globalSectionsOver_eq_moduleGlobalSections_comp`, which is `rfl`, so
`Iso.refl` serves as the comparison `Γ(X, −) ⋙ restrictScalars ≅ globalSectionsOver f` that
`Stacks.Cohomology.ModuleComparison.rightDerivedCompIso` asks for; that lemma then moves the
restriction of scalars across the `ℕ`-indexed right derived functor, which needs exactness of
restriction of scalars and nothing else. The second step is
`Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived`, which identifies
`Hⁿ(RF(X[0]))` with `RⁿF(X)` for *any* right derived functor `RF` on the unbounded derived
category, given K-injective resolutions; `AlgebraicGeometry.derivedGlobalSectionsOver` is such a
functor by `AlgebraicGeometry.derivedGlobalSectionsOver_isRightDerivedFunctor`, and the
resolutions are `AlgebraicGeometry.Scheme.Modules.exists_quasiIso_isKInjective`.

The derived categories are free `[HasDerivedCategory]` binders in the comparison itself, as in
`StacksFrontier/AlgebraicGeometry/DerivedGlobalSections.lean`, so a consumer may instantiate them
at any model; only the final transport, which feeds a statement baked at the standard model,
reinstates `Stacks.Algebraization.modulesHasDerivedCategory`.

**No `@[stacks 0A0M]` attribute is attached.** Not because anything below the properness clause
is missing — [Stacks, Tag 02O8] is proved, as
`Stacks.Cohomology.FormalFunctions.isCohomologyReesFinite`, and `h02O8` below is discharged from
it in `Completion/CohomologyAdicCompletionWhole.lean` — but because a tag goes only on a
declaration proving the whole of it, and the properness clause is one of [Stacks, Tag 0A0M]'s two
parts. Both parts together are
`Stacks.Algebraization.exists_shortExact_adicCompletion_cohomology_whole` of
`Completion/GeneralCohomologyAdicCompletion.lean`, which carries the tag.

## References

* [Stacks Project, Tag 0A0M](https://stacks.math.columbia.edu/tag/0A0M)
* [Stacks Project, Tag 02OB](https://stacks.math.columbia.edu/tag/02OB)
* [Stacks Project, Tag 02O8](https://stacks.math.columbia.edu/tag/02O8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.FormalFunctions (baseIdealSheaf baseRingHom)
open scoped ModuleCat.Algebra

universe w₁ w₂ u

namespace Stacks.Algebraization

section Comparison

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
  [HasDerivedCategory.{w₁} X.Modules] [HasDerivedCategory.{w₂} (ModuleCat.{u} A)]

/-- **The two models of `Hᵖ(X, ℱ)` over the base ring agree.** On the left, Mathlib's
`ℕ`-indexed right derived functor of `Γ(X, −) : X.Modules ⥤ ModuleCat Γ(X, 𝒪_X)`, computed by an
injective resolution and then restricted to `A`-modules along `baseRingHom`; on the right, the
degree-`q` cohomology, taken in the unbounded derived category of `A`-modules, of unbounded
derived global sections `RΓ(X, −)` applied to the sheaf placed in degree zero. Naturally in the
sheaf of modules. -/
def rightDerivedRestrictScalarsIso (q : ℕ) :
    (moduleGlobalSections X).rightDerived q ⋙ ModuleCat.restrictScalars (baseRingHom A f) ≅
      DerivedCategory.singleFunctor X.Modules 0 ⋙ derivedGlobalSectionsOver f ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} A) (q : ℤ) :=
  haveI := Stacks.Cohomology.CechAcyclic.preservesHomology_restrictScalars.{u} (baseRingHom A f)
  Stacks.Cohomology.ModuleComparison.rightDerivedCompIso (moduleGlobalSections X)
      (ModuleCat.restrictScalars (baseRingHom A f)) (globalSectionsOver f) (Iso.refl _) q ≪≫
    (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived (globalSectionsOver f)
      (derivedGlobalSectionsOver f) (derivedGlobalSectionsOverUnit f)
      (Scheme.Modules.exists_quasiIso_isKInjective X) q).symm

/-- **The comparison of the two models, whiskered with the adic tower.** This is the shape in
which the two towers of [Stacks, Tag 02OB] and of [Stacks, Tag 0A0M] are written: on the left the
tower `n ↦ Hᵖ(X, ℱ/𝓘ⁿℱ)` of `Γ(X, 𝒪_X)`-modules read over `A`, on the right the same tower formed
in the unbounded derived category. -/
def adicQuotientRightDerivedRestrictScalarsIso (𝓘 : X.IdealSheafData) (F : X.Modules) (q : ℕ) :
    (adicQuotientSystem 𝓘 F ⋙ (moduleGlobalSections X).rightDerived q) ⋙
        ModuleCat.restrictScalars (baseRingHom A f) ≅
      (adicQuotientSystem 𝓘 F ⋙ DerivedCategory.singleFunctor X.Modules 0 ⋙
          derivedGlobalSectionsOver f) ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} A) (q : ℤ) :=
  Functor.isoWhiskerLeft (adicQuotientSystem 𝓘 F) (rightDerivedRestrictScalarsIso f q)

/-- **The Mittag-Leffler condition crosses between the two models.** Restriction of scalars along
`baseRingHom` is exact, so it preserves the Mittag-Leffler condition of [Stacks, Tag 02N0]; the
resulting tower of `A`-modules is isomorphic to the tower formed in the unbounded derived
category by `adicQuotientRightDerivedRestrictScalarsIso`.

This is what carries the Mittag-Leffler clause of [Stacks, Tag 02OB] to the hypothesis `hML` of
`Stacks.Algebraization.exists_iso_cohomology_limit_adicQuotients_of_isMittagLeffler`. -/
theorem isMittagLefflerCategorical_homologyDerivedGlobalSections (𝓘 : X.IdealSheafData)
    (F : X.Modules) (q : ℕ)
    (h : IsMittagLefflerCategorical
      (adicQuotientSystem 𝓘 F ⋙ (moduleGlobalSections X).rightDerived q)) :
    IsMittagLefflerCategorical
      ((adicQuotientSystem 𝓘 F ⋙ DerivedCategory.singleFunctor X.Modules 0 ⋙
          derivedGlobalSectionsOver f) ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} A) (q : ℤ)) :=
  have : PreservesFiniteLimits (ModuleCat.restrictScalars.{u} (baseRingHom A f)) :=
    Stacks.Cohomology.CechAcyclic.preservesFiniteLimits_restrictScalars.{u} (baseRingHom A f)
  have : PreservesFiniteColimits (ModuleCat.restrictScalars.{u} (baseRingHom A f)) :=
    ⟨fun _ _ _ ↦ ⟨fun {_} ↦ inferInstance⟩⟩
  IsMittagLefflerCategorical.of_natIso
    (adicQuotientRightDerivedRestrictScalarsIso f 𝓘 F q).symm
    (IsMittagLefflerCategorical.map _ (ModuleCat.restrictScalars (baseRingHom A f)) h)

end Comparison

section Transport

attribute [local instance 10000] Stacks.Algebraization.modulesHasDerivedCategory
attribute [local instance] AlgebraicGeometry.modulesLinear
  Stacks.Cohomology.AffineBase.baseSectionsAlgebra

/-- **The properness conclusion of [Stacks, Tag 0A0M], granted [Stacks, Tag 02O8].** With the
hypotheses of `Stacks.Algebraization.exists_shortExact_cohomology_limit_adicQuotients` and `f`
proper, the `R¹lim` term of that tag's sequence vanishes in degree `q + 1`, so

`H^{q+1}(X, lim ℱ/𝓘ⁿℱ) ≅ lim H^{q+1}(X, ℱ/𝓘ⁿℱ)`.

The source gets the vanishing from the Mittag-Leffler condition of [Stacks, Tag 02OB] for the
tower `n ↦ Hᵖ(X, ℱ/𝓘ⁿℱ)` in degree `p - 1 = q`, and that is exactly how it is got here:
`Stacks.Cohomology.FormalFunctions.exists_uniform_bound_idealPowerQuotient_of_reesFinite` proves
the condition in the `(moduleGlobalSections X).rightDerived q` model, and
`isMittagLefflerCategorical_homologyDerivedGlobalSections` carries it to the unbounded model the
sequence is stated in.

The one hypothesis left is `h02O8`, [Stacks, Tag 02O8] — the Rees-finiteness of
`⨁ₙ Hᵖ(X, 𝓘ⁿℱ)` — carried in the general form quantified over every Noetherian base, ideal,
proper scheme, coherent module and degree. It is discharged, by
`Stacks.FormalFunctions.isReesFinite_cohomologyIdealPowerSystem`, which quantifies
`Stacks.Cohomology.FormalFunctions.isCohomologyReesFinite` over exactly that data; the module
holding it and this one do not import each other, so the discharge is performed in the leaf
`Completion/CohomologyAdicCompletionWhole.lean`, where
`Stacks.Algebraization.exists_iso_cohomology_limit_adicQuotients_of_isProper` is this statement
with `h02O8` gone. -/
theorem exists_iso_cohomology_limit_adicQuotients_of_reesFinite
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{u}} [IsNoetherian X] (f : X ⟶ Spec (.of A)) (F : X.Modules) [F.IsCoherent]
    (hfinite : ∀ p : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) p).obj
        ((derivedGlobalSectionsOver f).obj
          ((DerivedCategory.singleFunctor X.Modules 0).obj F))))
    (hf : AlgebraicGeometry.IsProper f) (q : ℕ)
    (h02O8 : ∀ (A' : Type u) [CommRing A'] [IsNoetherianRing A'] (I' : Ideal A')
      (X' : Over (Spec (.of A'))) (_ : AlgebraicGeometry.IsProper X'.hom)
      (F' : X'.left.Modules) (_ : SheafOfModules.IsCoherent F') (p' : ℕ),
      (Stacks.Cohomology.FormalFunctions.cohomologyIdealPowerSystem I' X' F' p').IsReesFinite) :
    Nonempty
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) ((q : ℤ) + 1)).obj
          ((derivedGlobalSectionsOver f).obj
            ((DerivedCategory.singleFunctor X.Modules 0).obj
              (limit (adicQuotientSystem (baseIdealSheaf A I f) F)))) ≅
        limit ((adicQuotientSystem (baseIdealSheaf A I f) F ⋙
              DerivedCategory.singleFunctor X.Modules 0 ⋙ derivedGlobalSectionsOver f) ⋙
          DerivedCategory.homologyFunctor (ModuleCat.{u} A) ((q : ℤ) + 1))) := by
  obtain ⟨-, -, hML, -⟩ :=
    Stacks.Cohomology.FormalFunctions.exists_uniform_bound_idealPowerQuotient_of_reesFinite
      I f F hf (Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent'_of_isCoherent
        inferInstance) q h02O8
  refine exists_iso_cohomology_limit_adicQuotients_of_isMittagLeffler A I f F hfinite
    ((q : ℤ) + 1) ?_
  rw [add_sub_cancel_right]
  exact isMittagLefflerCategorical_homologyDerivedGlobalSections f _ F q hML

end Transport

end Stacks.Algebraization

end
