module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.NormalizedDualizingExistence

/-!
# The trace of the normalized dualizing module of a rational surface singularity

In Situation [Stacks, Tag 0B4W] — a two-dimensional local normal Nagata domain `A` defining a
rational singularity and a modification `f : X ⟶ Spec(A)` with `X` normal — let `ω_A` be a
dualizing module of `A` and let `ω_X` be *the* dualizing module of `X`, the one normalized relative
to `ω_A` in the sense of [Stacks, Remark 0B4R]: `ω_X[2]` is `f^!(ω_A[2])`, that is
`AlgebraicGeometry.RationalSingularitySituation.DualizingNormalization`. [Stacks, Tag 0BBU]
asserts that the trace `H⁰(X, ω_X) ⟶ ω_A` is an isomorphism, and consequently that there is a
canonical map `f^*ω_A ⟶ ω_X`. Both are here.

## Main definitions

* `AlgebraicGeometry.RationalSingularitySituation.normalizedTrace` — the trace
  `H⁰(X, ω_X) ⟶ ω_A`: the counit `Rf_*f^!ω_A ⟶ ω_A` of Grothendieck duality, read in degree zero
  through the normalization `e : f^!ω_A ≅ ω_X`.
* `AlgebraicGeometry.RationalSingularitySituation.normalizedPullbackMap` — the canonical map
  `f^*ω_A ⟶ ω_X`, the adjunct of the inverse of the trace.

## Main results

* `AlgebraicGeometry.RationalSingularitySituation.bijective_normalizedTrace` —
  **[Stacks, Tag 0BBU]**, the trace is an isomorphism.
* `AlgebraicGeometry.RationalSingularitySituation.epi_normalizedPullbackMap_of_epi_counit` — the
  canonical map is surjective once `ω_X` is globally generated.

## Implementation notes

*What is assumed of `ω_X`.* Only the normalization of [Stacks, Remark 0B4R] that the source means
by "`ω_X` the dualizing module of `X`": `ω_X[2]` is the dualizing complex normalized relative to
`ω_A[2]`, i.e. an isomorphism `e : f^!(ω_A) ≅ ω_X` in degree zero, where `f^!` is the right adjoint
of `Rf_*` for the proper morphism `f` ([Stacks, Tag 0A9E], unconditional here). The source's proof
— Grauert–Riemenschneider vanishing and the duality sequence
`0 ⟶ f_*ω_X ⟶ ω_A ⟶ Ext²_A(R¹f_*𝒪_X, ω_A)` — is replaced by duality in degree zero against `𝒪_X`,
whose first cohomology vanishes because `A` defines a rational singularity:
`Hom(𝒪_X, ω_X) = Hom_A(Γ(X, 𝒪_X), ω_A)` reads `H⁰(X, ω_X) = ω_A` since `Γ(X, 𝒪_X) = A` ([Stacks,
Tag 0B4Y]). The duality isomorphisms used are
`AlgebraicGeometry.RationalSingularitySituation.bijective_normalizationPairing`, proved from the
adjunction `Rf_* ⊣ f^!` and the vanishing of `R^i f_*` above degree one (the fibres of `f` have
dimension at most one).

*The existence of `ω_X`* — that `f^!(ω_A[2])` is a dualizing complex concentrated in degree `-2` —
is the content of [Stacks, Remark 0B4R] and [Stacks, Example 0AWI] and is not part of this tag.

## References

* [Stacks Project, Tag 0BBU](https://stacks.math.columbia.edu/tag/0BBU)
* [Stacks Project, Tag 0B4W](https://stacks.math.columbia.edu/tag/0B4W)
* [Stacks Project, Tag 0B4R](https://stacks.math.columbia.edu/tag/0B4R)
* [Stacks Project, Tag 0B4Y](https://stacks.math.columbia.edu/tag/0B4Y)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.RationalSingularitySituation

variable (S : RationalSingularitySituation.{u}) [IsLocallyNoetherian S.X]
  {ωA : ModuleCat.{u} S.A} {ωX : S.X.Modules}

/-- The trace `H⁰(X, ω_X) ⟶ ω_A` of the dualizing module normalized relative to `ω_A`, the
normalization being an isomorphism `e : f^!(ω_A) ≅ ω_X` in degree zero: the counit
`Rf_*(f^!ω_A) ⟶ ω_A` of Grothendieck duality, read in degree zero through `e`. -/
abbrev normalizedTrace
    (e : (S.relativeDualizingComplex ωA).obj ≅
      (DerivedCategory.singleFunctor S.X.Modules 0).obj ωX) :
    S.globalSectionsModule ωX ⟶ ωA :=
  S.normalizationTrace ωA ωX e.inv

/-- **Stacks Project, Tag 0BBU.** In Situation [Stacks, Tag 0B4W], let `ω_A` be a dualizing
module of `A` and let `ω_X` be the dualizing module of `X` normalized relative to `ω_A`
([Stacks, Remark 0B4R]: `ω_X[2] = f^!(ω_A[2])`, here the isomorphism `e : f^!(ω_A) ≅ ω_X` in
degree zero). Then the trace map `H⁰(X, ω_X) ⟶ ω_A` is an isomorphism. The consequent canonical
map `f^*ω_A ⟶ ω_X` is `AlgebraicGeometry.RationalSingularitySituation.normalizedPullbackMap`.

The proof is duality in degree zero against `𝒪_X`: `H¹(X, 𝒪_X) = 0` because `A` defines a rational
singularity, so `Hom(𝒪_X, ω_X) ⟶ Hom_A(Γ(X, 𝒪_X), ω_A)` is bijective, and its source is
`H⁰(X, ω_X)` and its target `ω_A`, as `Γ(X, 𝒪_X) = A` ([Stacks, Tag 0B4Y]). -/
@[stacks 0BBU "the trace H^0(X, omega_X) -> omega_A of the dualizing module normalized \
relative to omega_A (Remark 0B4R: f^!(omega_A) = omega_X in degree zero) is an isomorphism; the \
canonical map f^*omega_A -> omega_X is normalizedPullbackMap"]
theorem bijective_normalizedTrace (_hωA : Stacks.Duality.IsDualizingRingModule S.A ωA)
    (e : (S.relativeDualizingComplex ωA).obj ≅
      (DerivedCategory.singleFunctor S.X.Modules 0).obj ωX) :
    Function.Bijective (S.normalizedTrace e).hom := by
  have hpair := S.bijective_normalizationPairing ωA ωX e.inv
    (SheafOfModules.unit S.X.ringCatSheaf) (_root_.isQuasicoherent_of_isCoherent _)
    (by
      let := HasDerivedCategory.standard S.X.Modules
      let := HasDerivedCategory.standard (ModuleCat.{u} Γ(S.X, ⊤))
      exact (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff _ 1 _).2
        S.isZero_firstCohomologyStructureSheaf)
  have hfun : S.normalizationPairing ωA ωX e.inv (SheafOfModules.unit S.X.ringCatSheaf) =
      S.tracePairing (S.normalizedTrace e) (SheafOfModules.unit S.X.ringCatSheaf) :=
    funext fun φ => S.normalizationPairing_eq ωA ωX e.inv _ φ
  rw [hfun] at hpair
  have hcomp : (S.unitGlobalSectionsHomEquiv ωA) ∘
      S.tracePairing (S.normalizedTrace e) (SheafOfModules.unit S.X.ringCatSheaf) =
      (S.normalizedTrace e).hom ∘ S.unitSectionHom ωX := rfl
  have h : Function.Bijective ((S.normalizedTrace e).hom ∘ S.unitSectionHom ωX) :=
    hcomp ▸ ((S.unitGlobalSectionsHomEquiv ωA).bijective.comp hpair)
  exact (Function.Bijective.of_comp_iff _ (S.bijective_unitSectionHom ωX)).1 h

/-- The trace of the normalized dualizing module, as an isomorphism `H⁰(X, ω_X) ≅ ω_A`. -/
def normalizedTraceIso (hωA : Stacks.Duality.IsDualizingRingModule S.A ωA)
    (e : (S.relativeDualizingComplex ωA).obj ≅
      (DerivedCategory.singleFunctor S.X.Modules 0).obj ωX) :
    S.globalSectionsModule ωX ≅ ωA :=
  haveI : IsIso (S.normalizedTrace e) :=
    (ConcreteCategory.isIso_iff_bijective _).2 (S.bijective_normalizedTrace hωA e)
  asIso (S.normalizedTrace e)

/-- **Stacks Project, Tag 0BBU, the canonical map.** The map `f^*ω_A ⟶ ω_X` induced by the trace
isomorphism of the normalized dualizing module: the adjunct, under
`M ↦ f^*M̃ ⊣ ℱ ↦ H⁰(X, ℱ)` (`globalSectionsAdjunction`), of the inverse of the trace. -/
@[stacks 0BBU "the canonical map f^*omega_A -> omega_X induced by the trace isomorphism, for the \
dualizing module normalized relative to omega_A"]
def normalizedPullbackMap (hωA : Stacks.Duality.IsDualizingRingModule S.A ωA)
    (e : (S.relativeDualizingComplex ωA).obj ≅
      (DerivedCategory.singleFunctor S.X.Modules 0).obj ωX) :
    (Scheme.Modules.pullback S.f).obj (tilde ωA) ⟶ ωX :=
  (S.globalSectionsAdjunction.homEquiv ωA ωX).symm
    ((S.normalizedTraceIso hωA e).inv ≫ (S.globalSectionsModuleIso ωX).inv)

/-- The canonical map is the counit of `globalSectionsAdjunction` at `ω_X`, precomposed with the
image of the inverse trace. -/
theorem normalizedPullbackMap_eq (hωA : Stacks.Duality.IsDualizingRingModule S.A ωA)
    (e : (S.relativeDualizingComplex ωA).obj ≅
      (DerivedCategory.singleFunctor S.X.Modules 0).obj ωX) :
    S.normalizedPullbackMap hωA e =
      (tilde.functor (CommRingCat.of S.A) ⋙ Scheme.Modules.pullback S.f).map
          ((S.normalizedTraceIso hωA e).inv ≫ (S.globalSectionsModuleIso ωX).inv) ≫
        S.globalSectionsAdjunction.counit.app ωX :=
  S.globalSectionsAdjunction.homEquiv_counit ωA ωX _

/-- The canonical map is an epimorphism as soon as `ω_X` is generated by its global sections:
the two differ by the image under the left adjoint of an isomorphism. -/
theorem epi_normalizedPullbackMap_of_epi_counit
    (hωA : Stacks.Duality.IsDualizingRingModule S.A ωA)
    (e : (S.relativeDualizingComplex ωA).obj ≅ (DerivedCategory.singleFunctor S.X.Modules 0).obj ωX)
    (h : Epi (S.globalSectionsAdjunction.counit.app ωX)) :
    Epi (S.normalizedPullbackMap hωA e) := by
  have h₁ : Epi ((tilde.functor (CommRingCat.of S.A) ⋙ Scheme.Modules.pullback S.f).map
      ((S.normalizedTraceIso hωA e).inv ≫ (S.globalSectionsModuleIso ωX).inv)) := inferInstance
  rw [S.normalizedPullbackMap_eq hωA e]
  exact @epi_comp _ _ _ _ _ _ h₁ _ h

/-- A dualizing module normalized in the sense of `DualizingNormalization` has the trace
isomorphism of [Stacks, Tag 0BBU]; this is `bijective_normalizedTrace` at its normalization. -/
theorem DualizingNormalization.bijective_normalizedTrace
    (hωA : Stacks.Duality.IsDualizingRingModule S.A ωA) (N : S.DualizingNormalization ωA ωX) :
    Function.Bijective (S.normalizedTrace N.normalizedIso).hom :=
  S.bijective_normalizedTrace hωA N.normalizedIso

end AlgebraicGeometry.RationalSingularitySituation

end
