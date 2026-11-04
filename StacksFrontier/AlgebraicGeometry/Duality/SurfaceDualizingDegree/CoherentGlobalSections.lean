module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentFinitePresentation
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorSingleBoundedBelow
public import StacksFrontier.AlgebraicGeometry.Duality.SurfaceDualizingDegree.CohomologyOverRing
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.DerivedSectionsTensorPseudoCoherence
public import StacksFrontier.AlgebraicGeometry.ProperCoherenceWitness.ChowStalk
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.Basic
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.ThickeningQuasicoherent
public import StacksFrontier.RingTheory.Dualizing.DerivedHomDuality.Duality

/-!
# `RΓ(X, ℱ)` is bounded with finite cohomology, for `ℱ` coherent and `X` proper over the base

Let `A` be a Noetherian ring, let `f : X ⟶ Spec A` be a proper morphism and let `ℱ` be a
coherent `𝒪_X`-module. This file proves that

`RΓ(X, ℱ) ∈ D^b_{Coh}(A)`,

that is: the `A`-module `Hⁱ(X, ℱ)` is finite for every `i : ℤ`, and `RΓ(X, ℱ)` is bounded for
the canonical t-structure on `D(A)`.

This is the side condition under which derived Hom into a dualizing complex is an
anti-equivalence ([Stacks, Tag 0A7C], `Dualizing.boundedCoherentDualizingDerivedHom_isEquivalence`
and `Dualizing.coherentDualizingDerivedHom_isEquivalence`), hence the condition under which a
nonzero morphism out of `RΓ(X, ℱ)` is carried to a nonzero morphism by that duality.

## Main definitions

* `AlgebraicGeometry.boundedCoherentDerivedGlobalSections` — `RΓ(X, ℱ)` as an object of
  `Dualizing.BoundedCoherentDerivedCategory A`, the bounded derived category of `A`-modules with
  finite cohomology, which is the source and target of the anti-equivalence of
  [Stacks, Tag 0A7C].

## Main results

* `AlgebraicGeometry.moduleFinite_cohomologyAsBaseModule` — `Hⁿ(X, ℱ)`, read over the base ring
  by restriction of scalars, is a finite `A`-module in every degree `n : ℕ`.
* `AlgebraicGeometry.moduleFinite_homology_derivedGlobalSections` — the degree-`i` cohomology of
  `RΓ(X, ℱ)` is a finite `A`-module for every `i : ℤ`.
* `AlgebraicGeometry.isGE_zero_derivedGlobalSections` and
  `AlgebraicGeometry.exists_isLE_derivedGlobalSections` — the two cohomological bounds, and
  `AlgebraicGeometry.bounded_derivedGlobalSections` — their conjunction, which is boundedness for
  the canonical t-structure.

## The proof

*Finiteness.* Below degree zero there is nothing to prove: `RΓ(X, -)` is the right derived
functor of global sections, so it carries a sheaf placed in degree zero to an object with no
cohomology in negative degrees, and a subsingleton module is finite. In degree `n ≥ 0`, the
degree-`n` cohomology of `RΓ(X, ℱ)` is the classical `Hⁿ(X, ℱ)` read over `A`
(`AlgebraicGeometry.cohomologyOverRingIsoDerivedCohomology`), and that is a finite `A`-module
because the higher direct images of a coherent module under a proper morphism are coherent
([Stacks, Tag 02O6]); this is the degree-`n` form of the argument that
`AlgebraicGeometry.moduleFinite_firstCohomologySheafAsBaseModule` runs in degree one.

*Boundedness.* The lower bound is the same vanishing in negative degrees. For the upper bound,
`X` is quasi-compact and quasi-separated, being proper over the spectrum of a ring, so `RΓ(X, -)`
has finite cohomological dimension on complexes with quasi-coherent cohomology
([Stacks, Tag 08D5], `AlgebraicGeometry.exists_isLE_derivedGlobalSectionsOver_obj`); a coherent
module placed in degree zero has quasi-coherent cohomology sheaves and lies in `D^{≤ 0}`. No
hypothesis on the dimension of `X` or of `A` is needed.

## Implementation notes

The finiteness statement in a fixed degree `n : ℕ` mentions no derived category, and is stated
with global sections spelled as `SheafOfModules.evaluation X.ringCatSheaf (op ⊤)` followed by
restriction of scalars along `A ≅ Γ(Spec A, 𝒪) ⟶ Γ(X, 𝒪_X)`, which is the spelling of
`AlgebraicGeometry.globalSectionsOver` and the left-hand side of
`AlgebraicGeometry.cohomologyOverRingIsoDerivedCohomology`. [Stacks, Tag 02O6] is stated with
the equal spelling `Stacks.Cohomology.AffineBase.moduleGlobalSections` and restriction along
`Γ(Spec A, 𝒪) ⟶ Γ(X, 𝒪_X)` alone, so the two differ by restriction along the isomorphism
`A ≅ Γ(Spec A, 𝒪)`, which is surjective; that is what
`Stacks.AlgebraicGeometry.ProperCohomologyFinite.moduleFinite_compHom_of_surjective` consumes.

The statements about the derived category are taken at the standard model. The locally small
model of [Stacks, Tag 079Q] arrives through the imports as a global instance, which a
default-priority file-local instance does not outrank, so the three global instances are erased
here and `HasDerivedCategory.standard` is installed in their place; this is the discipline of
`StacksFrontier/AlgebraicGeometry/Duality/StandardModelGlobalSections.lean`. The standard model is
forced rather than chosen: it is the model baked into the type of
`Dualizing.BoundedCoherentDerivedCategory` and of [Stacks, Tag 08D5] as formalized here.

The vanishing of `RΓ(X, ℱ)` in negative degrees is taken from the generic statement
`Stacks.DerivedFunctor.isGE_derived_single` for a right derived functor, whose
`HasDerivedCategory` arguments are binders, rather than from the reading of it for
`AlgebraicGeometry.derivedGlobalSectionsOver` at a fixed model.

## References

* [Stacks Project, Tag 0A7C](https://stacks.math.columbia.edu/tag/0A7C)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-! ### Finiteness of the cohomology of a coherent module over the base ring -/

/-- **`Hⁿ(X, ℱ)` is a finite module over the base ring**, for `f : X ⟶ Spec A` proper with `A`
Noetherian and `ℱ` coherent, in every degree `n`. The cohomology is read over `A` by restriction
of scalars along `A ≅ Γ(Spec A, 𝒪) ⟶ Γ(X, 𝒪_X)`.

The higher direct images of a coherent module under a proper morphism are coherent, and over an
affine base the sections of that coherent module are the cohomology ([Stacks, Tag 02O6]);
restricting scalars further along the isomorphism `A ≅ Γ(Spec A, 𝒪)` preserves finiteness. This
is the degree-`n` form of `AlgebraicGeometry.moduleFinite_firstCohomologySheafAsBaseModule`. -/
theorem moduleFinite_cohomologyAsBaseModule {A : Type u} [CommRing A] [IsNoetherianRing A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f] (ℱ : X.Modules) [ℱ.IsCoherent]
    (n : ℕ) :
    Module.Finite A
      ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
        (((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).rightDerived n).obj
          ℱ)) := by
  have : IsLocallyNoetherian (Spec (.of A)) := isLocallyNoetherian_Spec.mpr inferInstance
  have hΓ := ProperCoherenceWitness.moduleFinite_cohomology f ℱ n
  have hsurj : Function.Surjective (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).inv).2
  exact Stacks.AlgebraicGeometry.ProperCohomologyFinite.moduleFinite_compHom_of_surjective
    (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom hsurj
    ((ModuleCat.restrictScalars f.appTop.hom).obj
      (((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived n).obj ℱ))

/-! ### `RΓ(X, ℱ)` in the bounded derived category with finite cohomology -/

attribute [local instance] HasDerivedCategory.standard

section Derived

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-- **`RΓ(X, ℱ)` has no cohomology in negative degrees.** Derived global sections over the base
is the right derived functor of global sections, and a right derived functor carries an object
placed in degree zero into `D^{≥ 0}`. -/
theorem isGE_zero_derivedGlobalSections (ℱ : X.Modules) :
    ((derivedGlobalSectionsOver f).obj
      ((DerivedCategory.singleFunctor X.Modules 0).obj ℱ)).IsGE 0 :=
  Stacks.DerivedFunctor.isGE_derived_single (globalSectionsOver f)
    (derivedGlobalSectionsOver f) (derivedGlobalSectionsOverUnit f)
    (Scheme.Modules.exists_quasiIso_isKInjective X) ℱ

/-- **`RΓ(X, ℱ)` is bounded above**, for `f : X ⟶ Spec A` proper and `ℱ` quasi-coherent. A
scheme proper over the spectrum of a ring is quasi-compact and quasi-separated, so derived global
sections over the base has finite cohomological dimension on complexes with quasi-coherent
cohomology ([Stacks, Tag 08D5]), and a quasi-coherent module placed in degree zero has
quasi-coherent cohomology sheaves and lies in `D^{≤ 0}`. -/
theorem exists_isLE_derivedGlobalSections [IsProper f] (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    ∃ n : ℤ, ((derivedGlobalSectionsOver f).obj
      ((DerivedCategory.singleFunctor X.Modules 0).obj ℱ)).IsLE n := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  obtain ⟨N, hN⟩ := exists_isLE_derivedGlobalSectionsOver_obj f
  exact ⟨0 + N, hN _ 0
    (fun i => Stacks.Thickenings.isQuasicoherent_homology_singleFunctor_obj X ℱ
      inferInstance i) inferInstance⟩

/-- **`RΓ(X, ℱ)` is bounded** for the canonical t-structure on `D(A)`, for `f : X ⟶ Spec A`
proper and `ℱ` quasi-coherent: `AlgebraicGeometry.isGE_zero_derivedGlobalSections` below and
`AlgebraicGeometry.exists_isLE_derivedGlobalSections` above. -/
theorem bounded_derivedGlobalSections [IsProper f] (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    (DerivedCategory.TStructure.t).bounded
      ((derivedGlobalSectionsOver f).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj ℱ)) :=
  ⟨⟨0, isGE_zero_derivedGlobalSections f ℱ⟩, exists_isLE_derivedGlobalSections f ℱ⟩

/-- **The cohomology of `RΓ(X, ℱ)` is a finite `A`-module in every degree**, for `f : X ⟶ Spec A`
proper with `A` Noetherian and `ℱ` coherent.

In negative degrees the cohomology vanishes, by
`AlgebraicGeometry.isGE_zero_derivedGlobalSections`, and a subsingleton module is finite. In
degree `n ≥ 0` the cohomology is the classical `Hⁿ(X, ℱ)` read over `A`, by
`AlgebraicGeometry.cohomologyOverRingIsoDerivedCohomology`, and that module is finite by
`AlgebraicGeometry.moduleFinite_cohomologyAsBaseModule`. -/
theorem moduleFinite_homology_derivedGlobalSections [IsNoetherianRing A] [IsProper f]
    (ℱ : X.Modules) [ℱ.IsCoherent] (i : ℤ) :
    Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
      ((derivedGlobalSectionsOver f).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj ℱ))) := by
  rcases lt_or_ge i 0 with hi | hi
  · have := isGE_zero_derivedGlobalSections f ℱ
    have hzero : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
        ((derivedGlobalSectionsOver f).obj
          ((DerivedCategory.singleFunctor X.Modules 0).obj ℱ))) :=
      DerivedCategory.isZero_of_isGE _ 0 i hi
    have : Subsingleton ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
        ((derivedGlobalSectionsOver f).obj
          ((DerivedCategory.singleFunctor X.Modules 0).obj ℱ))) :=
      (ModuleCat.isZero_iff_subsingleton).1 hzero
    exact Module.Finite.of_finite
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = (n : ℤ) := ⟨i.toNat, (Int.toNat_of_nonneg hi).symm⟩
    have := moduleFinite_cohomologyAsBaseModule f ℱ n
    exact Module.Finite.equiv (R := A)
      (cohomologyOverRingIsoDerivedCohomology f ℱ n).toLinearEquiv

/-- **`RΓ(X, ℱ) ∈ D^b_{Coh}(A)`**: for `f : X ⟶ Spec A` proper with `A` Noetherian and `ℱ`
coherent, derived global sections of `ℱ` over the base is an object of the bounded derived
category of `A`-modules with finite cohomology.

This is the category on which derived Hom into a dualizing complex for `A` is an
anti-equivalence, [Stacks, Tag 0A7C]
(`Dualizing.boundedCoherentDualizingDerivedHom_isEquivalence`). -/
def boundedCoherentDerivedGlobalSections [IsNoetherianRing A] [IsProper f]
    (ℱ : X.Modules) [ℱ.IsCoherent] :
    Dualizing.BoundedCoherentDerivedCategory.{u, u} A :=
  haveI : ℱ.IsQuasicoherent := isQuasicoherent_of_isCoherent ℱ
  ⟨(derivedGlobalSectionsOver f).obj ((DerivedCategory.singleFunctor X.Modules 0).obj ℱ),
    moduleFinite_homology_derivedGlobalSections f ℱ,
    bounded_derivedGlobalSections f ℱ⟩

end Derived

end AlgebraicGeometry

end
