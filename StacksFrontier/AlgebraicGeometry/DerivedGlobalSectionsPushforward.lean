module

public import StacksFrontier.AlgebraicGeometry.DerivedPushforward

/-!
# Derived global sections over the base are derived pushforward to the base

Let `A` be a commutative ring and let `f : X ⟶ Spec A` be a scheme over `A`. The development
carries two functors out of the unbounded derived category of `𝒪_X`-modules that both deserve
the name *derived global sections over the base*:

* `AlgebraicGeometry.derivedGlobalSectionsOver f : D(𝒪_X) ⥤ D(A)`, the total right derived
  functor of `A`-linear global sections `Γ(X, -)`, whose cohomology is
  `AlgebraicGeometry.cohomologyOverField` for a scheme over a field; and
* `Stacks.Duality.derivedPushforward f : D(𝒪_X) ⥤ D(𝒪_{Spec A})`, the total right derived
  functor of direct image, the `Rf_*` of the `D_QCoh` development and of [Stacks, Tag 0A9E].

This file identifies them: `Γ(Spec A, f_* ℱ) = Γ(X, ℱ)` on the nose as `A`-modules
(`pushforwardGlobalSectionsOverIso` is the identity transformation), and deriving both sides
produces the canonical comparison

`R Γ(X, -) ⟶ R Γ(Spec A, -) ∘ Rf_*`

whose invertibility is [Stacks, Tag 0D5W]. The comparison is characterized by one equation, its
invertibility is reduced to a single statement about K-injective complexes, and it is proved
invertible for a morphism with exact pullback — in particular for a flat morphism. The shape is
that of `AlgebraicGeometry.lerayComparison`, of which this is the case `V = ⊤` read with the
base ring `A` in place of `Γ(Spec A, 𝒪)`.

## Main definitions

* `AlgebraicGeometry.pushforwardGlobalSectionsOverIso` — the identification
  `Γ(Spec A, f_* -) = Γ(X, -)` of `A`-linear functors.
* `AlgebraicGeometry.baseLerayUnit` and `AlgebraicGeometry.baseLerayComparison` — the canonical
  transformation `Γ(X, -) ⟶ Qh ⋙ (Rf_* ⋙ RΓ(Spec A, -))` and the comparison of derived
  functors it induces.
* `AlgebraicGeometry.derivedGlobalSectionsOverIsoDerivedPushforward` — the natural isomorphism
  `R Γ(X, -) ≅ R Γ(Spec A, -) ∘ Rf_*`, for a morphism with exact pullback.

## Main results

* `AlgebraicGeometry.baseLerayComparison_fac` and `AlgebraicGeometry.baseLerayComparison_ext` —
  the equation characterizing the comparison, and the uniqueness it gives.
* `AlgebraicGeometry.isIso_baseLerayComparison_iff` — the comparison is invertible exactly when
  the unit of `RΓ(Spec A, -)` is invertible at the direct image of every K-injective complex of
  `𝒪_X`-modules.
* `AlgebraicGeometry.isIso_baseLerayComparison_of_isKInjective_pushforward` and
  `AlgebraicGeometry.isIso_baseLerayComparison_of_preservesFiniteLimits_pullback` — two
  sufficient conditions.

## Implementation notes

**Why the identification of the underlying functors is the identity.** `A`-linear global
sections of `f_* ℱ` on `Spec A` are the sections of `ℱ` over `f⁻¹ ⊤ = ⊤`, read as an `A`-module
by restriction of scalars along `A ≅ Γ(Spec A, 𝒪) ⟶ Γ(Spec A, 𝒪) ⟶ Γ(X, 𝒪_X)`, and the two
restrictions of scalars compose to the one restriction of scalars that
`AlgebraicGeometry.globalSectionsOver f` uses. Each of these steps holds definitionally, so
`pushforwardGlobalSectionsOverIso` is `Iso.refl`; nothing of the comparison is hidden in it, and
all of the content sits in the invertibility statement.

**The derived categories in force are the locally small ones**,
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` and `ModuleCat.hasDerivedCategory`, as in
`StacksFrontier/AlgebraicGeometry/DerivedGlobalSections.lean` and
`StacksFrontier/AlgebraicGeometry/DerivedPushforward.lean`. That is the model the `D_QCoh`
development of `Stacks.Duality` is written against, so this file composes with it; at
`CategoryTheory.HasDerivedCategory.standard` the two sides would be different categories.

**What is not proved here.** [Stacks, Tag 0D5W] asserts the invertibility with no hypothesis on
`f` at all, and the unconditional statement is available in this library for *ringed spaces*, as
`Stacks.Cohomology.DerivedSectionsLeray.isIso_lerayComparison_top`; its proof is the
unconditional composition formula [Stacks, Tag 0D5T] rather than preservation of K-injectivity,
which direct image genuinely fails. That statement is pinned to
`CategoryTheory.HasDerivedCategory.standard` and is phrased for
`SheafOfModules (structureSheafRing X.toRingedSpace)` and the ringed-space derived pushforward,
so transporting it to the scheme-and-locally-small-model statement proved here is a change of
both model and spelling and is not carried out; what is recorded instead is the reduction
`isIso_baseLerayComparison_iff` and the exact-pullback case. The implementation notes of
`StacksFrontier/AlgebraicGeometry/DerivedPushforward.lean` say that the unconditional statement
"is not available here" and is "waiting on" the left derived pullback; that is accurate for the
scheme-level Leray comparison of that file, but it should not be read as saying that
[Stacks, Tag 0D5W] is absent from the library.

## References

* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
* [Stacks Project, Tag 0D5T](https://stacks.math.columbia.edu/tag/0D5T)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor Opposite
open Stacks.Cohomology.Localization (derivedUnit_isIsoOnKInjective natTrans_isIso_of_kInjectives)

universe u

namespace AlgebraicGeometry

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-! ### The identification of the underlying functors -/

/-- **`A`-linear global sections of a direct image are `A`-linear global sections.** The
identification `Γ(Spec A, f_* ℱ) = Γ(X, ℱ)` of `A`-modules, which holds on the nose: it is the
identity natural transformation. -/
def pushforwardGlobalSectionsOverIso :
    Scheme.Modules.pushforward f ⋙ globalSectionsOver (𝟙 (Spec (.of A))) ≅ globalSectionsOver f :=
  Iso.refl _

/-! ### The comparison -/

/-- The canonical transformation from termwise `A`-linear global sections on `X` to the composite
of the two chosen derived functors: the identification `Γ(Spec A, f_* -) = Γ(X, -)`, followed by
the unit of `RΓ(Spec A, -)` and then the unit of `Rf_*`. -/
def baseLerayUnit :
    homotopyGlobalSectionsOver f ⟶ DerivedCategory.Qh ⋙
      (Stacks.Duality.derivedPushforward f ⋙ derivedGlobalSectionsOver (𝟙 (Spec (.of A)))) :=
  Functor.whiskerRight
      (Functor.mapHomotopyCategoryCompIso (pushforwardGlobalSectionsOverIso f)
        (ComplexShape.up ℤ)).inv DerivedCategory.Qh ≫
    Functor.whiskerLeft
      ((Scheme.Modules.pushforward f).mapHomotopyCategory (ComplexShape.up ℤ))
      (derivedGlobalSectionsOverUnit (𝟙 (Spec (.of A)))) ≫
    Functor.whiskerRight (derivedPushforwardUnit f)
      (derivedGlobalSectionsOver (𝟙 (Spec (.of A))))

/-- **The comparison `RΓ(X, -) ⟶ RΓ(Spec A, -) ∘ Rf_*`**, the transformation induced by
`baseLerayUnit` through the universal property of the right derived functor of `A`-linear global
sections on `X`. By `baseLerayComparison_fac` its composite with
`derivedGlobalSectionsOverUnit` is `baseLerayUnit`, and by `baseLerayComparison_ext` that
equation determines it. [Stacks, Tag 0D5W] asserts that it is an isomorphism; see
`isIso_baseLerayComparison_iff`. -/
def baseLerayComparison :
    derivedGlobalSectionsOver f ⟶
      Stacks.Duality.derivedPushforward f ⋙ derivedGlobalSectionsOver (𝟙 (Spec (.of A))) :=
  (derivedGlobalSectionsOver f).rightDerivedDesc (derivedGlobalSectionsOverUnit f)
    (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) _ (baseLerayUnit f)

/-- The equation characterizing the comparison: composing it with the unit of `RΓ(X, -)`
recovers `baseLerayUnit`. -/
theorem baseLerayComparison_fac :
    derivedGlobalSectionsOverUnit f ≫
        Functor.whiskerLeft DerivedCategory.Qh (baseLerayComparison f) =
      baseLerayUnit f :=
  (derivedGlobalSectionsOver f).rightDerived_fac (derivedGlobalSectionsOverUnit f)
    (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) _ (baseLerayUnit f)

/-- The equation of `baseLerayComparison_fac` determines the comparison: two transformations out
of `RΓ(X, -)` that agree after composition with the unit are equal. -/
theorem baseLerayComparison_ext
    {G : DerivedCategory X.Modules ⥤ DerivedCategory (ModuleCat.{u} A)}
    (τ₁ τ₂ : derivedGlobalSectionsOver f ⟶ G)
    (h : derivedGlobalSectionsOverUnit f ≫ Functor.whiskerLeft DerivedCategory.Qh τ₁ =
      derivedGlobalSectionsOverUnit f ≫ Functor.whiskerLeft DerivedCategory.Qh τ₂) :
    τ₁ = τ₂ :=
  (derivedGlobalSectionsOver f).rightDerived_ext (derivedGlobalSectionsOverUnit f)
    (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) _ _ _ h

/-! ### Invertibility -/

/-- At a K-injective complex `I` of `𝒪_X`-modules, `baseLerayUnit` is invertible exactly when
the unit of `RΓ(Spec A, -)` is invertible at the direct image `f_* I`: the other two factors of
`baseLerayUnit` are invertible there, the first because it is a component of an isomorphism and
the third because the unit of `Rf_*` is invertible at a K-injective complex. -/
theorem isIso_baseLerayUnit_app_iff (I : CochainComplex X.Modules ℤ) [I.IsKInjective] :
    IsIso ((baseLerayUnit f).app
        ((HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).obj I)) ↔
      IsIso ((derivedGlobalSectionsOverUnit (𝟙 (Spec (.of A)))).app
        (((Scheme.Modules.pushforward f).mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).obj I))) := by
  have hunit := derivedUnit_isIsoOnKInjective (Stacks.Duality.homotopyPushforward f)
    (Stacks.Duality.derivedPushforward f) (derivedPushforwardUnit f) I
  have hmap : IsIso ((derivedGlobalSectionsOver (𝟙 (Spec (.of A)))).map
    ((derivedPushforwardUnit f).app
      ((HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).obj I))) := inferInstance
  dsimp only [baseLerayUnit, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  rw [isIso_comp_left_iff, isIso_comp_right_iff]

/-- **The formal half of [Stacks, Tag 0D5W] over the base.** The comparison
`RΓ(X, -) ⟶ RΓ(Spec A, -) ∘ Rf_*` is an isomorphism **if and only if** the unit of
`RΓ(Spec A, -)` is invertible at `f_* I` for every K-injective complex `I` of `𝒪_X`-modules.

Both implications are the universal property of the right derived functor of `Γ(X, -)` together
with the fact that its unit, and the unit of `Rf_*`, are invertible at K-injective complexes;
the reduction to K-injective complexes is possible because every complex of `𝒪_X`-modules admits
a quasi-isomorphism into one. -/
theorem isIso_baseLerayComparison_iff :
    IsIso (baseLerayComparison f) ↔
      ∀ (I : CochainComplex X.Modules ℤ) [I.IsKInjective],
        IsIso ((derivedGlobalSectionsOverUnit (𝟙 (Spec (.of A)))).app
          (((Scheme.Modules.pushforward f).mapHomotopyCategory (ComplexShape.up ℤ)).obj
            ((HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).obj I))) := by
  have key : ∀ (I : CochainComplex X.Modules ℤ) [I.IsKInjective],
      IsIso ((baseLerayComparison f).app (DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).obj I))) ↔
        IsIso ((baseLerayUnit f).app
          ((HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).obj I)) := by
    intro I _
    have := derivedUnit_isIsoOnKInjective (homotopyGlobalSectionsOver f)
      (derivedGlobalSectionsOver f) (derivedGlobalSectionsOverUnit f) I
    have heq : (derivedGlobalSectionsOverUnit f).app
          ((HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).obj I) ≫
        (baseLerayComparison f).app (DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).obj I)) =
          (baseLerayUnit f).app
            ((HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).obj I) := by
      simpa using NatTrans.congr_app (baseLerayComparison_fac f)
        ((HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).obj I)
    rw [← heq, isIso_comp_left_iff]
  refine ⟨fun _ I _ => ?_, fun h => natTrans_isIso_of_kInjectives _ fun I _ => ?_⟩
  · exact (isIso_baseLerayUnit_app_iff f I).1 ((key I).1 inferInstance)
  · exact (key I).2 ((isIso_baseLerayUnit_app_iff f I).2 (h I))

/-- **The comparison is invertible when direct image preserves K-injectivity.** If `f_*` carries
K-injective complexes of `𝒪_X`-modules to K-injective complexes of `𝒪_{Spec A}`-modules then
the comparison is an isomorphism, since the unit of a right derived functor is invertible at a
K-injective complex. -/
theorem isIso_baseLerayComparison_of_isKInjective_pushforward
    (h : ∀ I : CochainComplex X.Modules ℤ, I.IsKInjective →
      CochainComplex.IsKInjective
        (((Scheme.Modules.pushforward f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) :
    IsIso (baseLerayComparison f) := by
  rw [isIso_baseLerayComparison_iff]
  intro I hI
  have := h I hI
  exact derivedUnit_isIsoOnKInjective (homotopyGlobalSectionsOver (𝟙 (Spec (.of A))))
    (derivedGlobalSectionsOver (𝟙 (Spec (.of A))))
    (derivedGlobalSectionsOverUnit (𝟙 (Spec (.of A))))
    (((Scheme.Modules.pushforward f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)

/-- **The comparison is invertible for a morphism with exact pullback, in particular for a flat
morphism.** If `f^* : (Spec A).Modules ⥤ X.Modules` preserves finite limits — it always
preserves finite colimits, being a left adjoint, so this is exactly exactness of `f^*`, i.e.
flatness of `f` — then `RΓ(X, -) ⟶ RΓ(Spec A, -) ∘ Rf_*` is an isomorphism.

This is the adjoint criterion for K-injectivity [Stacks, Tag 08BJ] applied to `f^* ⊣ f_*`, fed
to `isIso_baseLerayComparison_of_isKInjective_pushforward`. -/
theorem isIso_baseLerayComparison_of_preservesFiniteLimits_pullback
    [Limits.PreservesFiniteLimits (Scheme.Modules.pullback f)] :
    IsIso (baseLerayComparison f) :=
  isIso_baseLerayComparison_of_isKInjective_pushforward f fun I hI =>
    have := hI
    CochainComplex.isKInjective_mapHomologicalComplex_of_exact _ _
      (Scheme.Modules.pullbackPushforwardAdjunction f) I

/-- **Derived global sections over the base are derived pushforward to the base.** For a scheme
`f : X ⟶ Spec A` with exact pullback — in particular for a flat `f` — the total right derived
functor `RΓ(X, -) : D(𝒪_X) ⥤ D(A)` of `A`-linear global sections is derived direct image `Rf_*`
followed by derived global sections on `Spec A`.

This is the identification of the two spellings of derived global sections over the base: the
`AlgebraicGeometry.derivedGlobalSectionsOver` whose cohomology is
`AlgebraicGeometry.cohomologyOverField`, and the `Stacks.Duality.derivedPushforward` that the
right adjoint of [Stacks, Tag 0A9E] is stated for. -/
def derivedGlobalSectionsOverIsoDerivedPushforward
    [Limits.PreservesFiniteLimits (Scheme.Modules.pullback f)] :
    derivedGlobalSectionsOver f ≅
      Stacks.Duality.derivedPushforward f ⋙ derivedGlobalSectionsOver (𝟙 (Spec (.of A))) :=
  have := isIso_baseLerayComparison_of_preservesFiniteLimits_pullback f
  asIso (baseLerayComparison f)

end AlgebraicGeometry

end
