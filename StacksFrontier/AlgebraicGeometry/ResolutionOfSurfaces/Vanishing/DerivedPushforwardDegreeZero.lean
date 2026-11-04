module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorSingleBoundedBelow
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.ModificationGlobalSections
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.PuncturedBaseCohomology
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedSectionExact
public import StacksFrontier.RingTheory.LocalRing.ShiftedResidueFieldDerivedHom
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `Rf_*𝒪_X` in degrees `≤ 0`, and the vanishing it makes available

Let `f : X ⟶ Spec A` be a morphism of schemes and let `K` be an object of `D(A)` which is
`Rf_*𝒪_X` in the sense of `AlgebraicGeometry.IsDerivedPushforwardStructureSheaf`. This file
reads off the two facts about `K` in degrees `≤ 0` that the vanishing statement of
[Stacks, Tag 0AXC] consumes: `K` has no cohomology in negative degrees, so it is `≥ 0` for the
canonical t-structure; and when `f` is a modification of the spectrum of a normal domain its
cohomology in degree zero is `A`.

Together with
`Stacks.NormalLocalDomain.hom_residueFieldShift_eq_zero_of_comp_mkQ_eq_zero` these give, in the
vanishing situation of [Stacks, Tag 0AX8], one of the two clauses of
`AlgebraicGeometry.VanishingSituation.ExtensionClassOfDerivedHom`: a morphism
`α : κ[-1] ⟶ Rf_*𝒪_X` whose restriction along `A[-1] ⟶ κ[-1]` vanishes is itself zero.

## Main results

* `AlgebraicGeometry.IsDerivedPushforwardStructureSheaf.isGE_zero`: `K` is `≥ 0`.
* `AlgebraicGeometry.IsDerivedPushforwardStructureSheaf.nonempty_homologyZeroIsoBase`:
  `H⁰(K) ≅ A` for a modification of the spectrum of a normal domain.
* `AlgebraicGeometry.VanishingSituation.hom_residueFieldShift_eq_zero_of_comp_mkQ_eq_zero`: in
  Situation [Stacks, Tag 0AX8], a morphism `κ[-1] ⟶ K` killed by precomposition with the shift
  of `A ⟶ κ` is zero.

## Implementation notes

`IsGE 0` is `DerivedCategory.isGE_iff` applied to the field `isZero_homology_neg`, which is
exactly the vanishing it asks for.

For `H⁰(K) ≅ A` the field `nonempty_homology_iso` in degree zero gives
`H⁰(K) ≅ R⁰Γ(X, 𝒪_X)`, and `R⁰` of a left exact functor is the functor itself by
`CategoryTheory.Functor.rightDerivedZeroIsoSelf`. Left exactness of `A`-linear global sections
holds because `AlgebraicGeometry.globalSectionsOver` is by definition evaluation at the
terminal open followed by restriction of scalars: evaluation is left exact on any site by
`Stacks.SheafOfModules.evaluationPreservesFiniteLimits`, and restriction of scalars preserves
limits. What remains is `Γ(X, 𝒪_X) ≅ A`, which for a modification of the spectrum of a normal
domain is `AlgebraicGeometry.IsModification.isIso_appTop`; the isomorphism is transported to
`ModuleCat` by hand because the ring map `A ⟶ Γ(X, 𝒪_X)` being inverted is the very map along
which scalars are restricted, so it is `A`-linear for the structure in question.

Only `Nonempty` of the degree-zero isomorphism is produced, since `nonempty_homology_iso` is
itself existential and no compatibility is required of the isomorphism.

## References

* [Stacks Project, Tag 0AXC](https://stacks.math.columbia.edu/tag/0AXC)
* [Stacks Project, Tag 0AX8](https://stacks.math.columbia.edu/tag/0AX8)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-- `A`-linear global sections is left exact: it is evaluation at the terminal open, which is
left exact on any site, followed by restriction of scalars, which preserves limits. -/
instance preservesFiniteLimits_globalSectionsOver :
    PreservesFiniteLimits (globalSectionsOver f) := by
  refine @comp_preservesFiniteLimits _ _ _ _ _ _ _ _ ?_ ?_
  · exact SheafOfModules.Finite.evaluationPreservesFiniteLimits _ _
  · have h := ((Functor.exact_tfae
        (ModuleCat.restrictScalars (((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom))).out 2 4).mp
      (ModuleCat.restrictScalars_map_exact _)
    exact h.1

/-- `A`-linear global sections is left exact at the sheaf-of-modules spelling too. -/
instance preservesFiniteLimits_secsOver : PreservesFiniteLimits (secsOver f) :=
  inferInstanceAs (PreservesFiniteLimits (globalSectionsOver f))

/-- **The global functions of a modification of the spectrum of a normal domain, as an
`A`-module, are `A`.** The ring map being inverted is the one along which scalars are
restricted, so the inverse of `AlgebraicGeometry.IsModification.isIso_appTop` is `A`-linear for
that structure. -/
def modificationSecsOverUnitIso [IsNormalDomain A] (hf : IsModification f) :
    (secsOver f).obj (SheafOfModules.unit X.ringCatSheaf) ≅ ModuleCat.of A A := by
  have hiso : IsIso ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop) := by
    have := hf.isIso_appTop
    infer_instance
  let φ := ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop)
  let l : A →ₗ[A] ((secsOver f).obj (SheafOfModules.unit X.ringCatSheaf)) :=
    { toFun := φ.hom
      map_add' := φ.hom.map_add
      map_smul' := fun a b => φ.hom.map_mul a b }
  have : IsIso (ModuleCat.ofHom l) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (ConcreteCategory.bijective_of_isIso φ)
  exact (asIso (ModuleCat.ofHom l)).symm

/-! ### The same two facts for the derived global sections of an arbitrary module -/

/-- **`RΓ(X, ℱ)` has no cohomology in negative degrees**, for any sheaf of modules `ℱ` placed in
degree zero, so it is `≥ 0` for the canonical t-structure on `D(A)`. This is the object-general
form of `IsDerivedPushforwardStructureSheaf.isGE_zero`, needed at the cokernel of
multiplication by a base scalar and not only at the structure sheaf. -/
theorem isGE_zero_derivedGlobalSectionsSingle (M : X.Modules) :
    ((derivedGlobalSectionsOver f).obj
      ((DerivedCategory.singleFunctor X.Modules 0).obj M)).IsGE 0 :=
  (DerivedCategory.isGE_iff _ 0).2 fun i hi =>
    Stacks.DerivedFunctor.isZero_homologyFunctor_obj_derived_single (globalSectionsOver f)
      (derivedGlobalSectionsOver f) (derivedGlobalSectionsOverUnit f)
      (Scheme.Modules.exists_quasiIso_isKInjective X) M i hi

/-- **`H⁰(RΓ(X, -)) ≅ Γ(X, -)` on sheaves placed in degree zero**, as an isomorphism of
functors: the cohomology in degree `n` of `RΓ(X, ℱ[0])` is `RⁿΓ(X, ℱ)`, and `R⁰` of a left exact
functor is the functor itself. -/
def derivedGlobalSectionsSingleHomologyZeroNatIso :
    DerivedCategory.singleFunctor X.Modules 0 ⋙ derivedGlobalSectionsOver f ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0 ≅ globalSectionsOver f :=
  Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived (globalSectionsOver f)
      (derivedGlobalSectionsOver f) (derivedGlobalSectionsOverUnit f)
      (Scheme.Modules.exists_quasiIso_isKInjective X) 0 ≪≫
    (globalSectionsOver f).rightDerivedZeroIsoSelf

/-- **The degree-zero cohomology of `RΓ(X, ℱ)` is `Γ(X, ℱ)`**, for any sheaf of modules `ℱ`
placed in degree zero: the component at `ℱ` of
`AlgebraicGeometry.derivedGlobalSectionsSingleHomologyZeroNatIso`. -/
def derivedGlobalSectionsSingleHomologyZeroIso (M : X.Modules) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
        ((derivedGlobalSectionsOver f).obj
          ((DerivedCategory.singleFunctor X.Modules 0).obj M)) ≅
      (globalSectionsOver f).obj M :=
  (derivedGlobalSectionsSingleHomologyZeroNatIso f).app M

/-- **The degree-zero identification of `RΓ(X, -)` is natural in the sheaf**: it carries the map
induced on `H⁰(RΓ(X, -))` by a morphism of sheaves to the map induced on `Γ(X, -)`. -/
theorem derivedGlobalSectionsSingleHomologyZeroIso_hom_naturality {M N : X.Modules} (φ : M ⟶ N) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
          ((derivedGlobalSectionsOver f).map
            ((DerivedCategory.singleFunctor X.Modules 0).map φ)) ≫
        (derivedGlobalSectionsSingleHomologyZeroIso f N).hom =
      (derivedGlobalSectionsSingleHomologyZeroIso f M).hom ≫ (globalSectionsOver f).map φ :=
  (derivedGlobalSectionsSingleHomologyZeroNatIso f).hom.naturality φ

namespace IsDerivedPushforwardStructureSheaf

variable {f}

/-- **`Rf_*𝒪_X` has no cohomology in negative degrees**, so it is `≥ 0` for the canonical
t-structure on `D(A)`. -/
theorem isGE_zero {K : DerivedCategory (ModuleCat.{u} A)}
    (hK : IsDerivedPushforwardStructureSheaf X f K) : K.IsGE 0 :=
  (DerivedCategory.isGE_iff K 0).2 fun i hi => hK.isZero_homology_neg i hi

/-- **The degree-zero cohomology of `Rf_*𝒪_X` is `A`**, for `f` a modification of the spectrum
of a normal domain: it is `R⁰Γ(X, 𝒪_X) = Γ(X, 𝒪_X)`, and the global functions of such a
modification are `A`. -/
@[ega "III 4.3.12" "special case"]
theorem nonempty_homologyZeroIsoBase [IsNormalDomain A] (hf : IsModification f)
    {K : DerivedCategory (ModuleCat.{u} A)} (hK : IsDerivedPushforwardStructureSheaf X f K) :
    Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj K ≅
      ModuleCat.of A A) :=
  ⟨(hK.nonempty_homology_iso 0).some ≪≫
    ((secsOver f).rightDerivedZeroIsoSelf.app (SheafOfModules.unit X.ringCatSheaf)) ≪≫
    modificationSecsOverUnitIso f hf⟩

end IsDerivedPushforwardStructureSheaf

namespace VanishingSituation

/-- **One of the two clauses of `ExtensionClassOfDerivedHom`, proved.** In Situation
[Stacks, Tag 0AX8], let `K` be `Rf_*𝒪_X` in the sense of
`IsDerivedPushforwardStructureSheaf`. A morphism `α : κ[-1] ⟶ K` whose precomposition with the
shift of the quotient map `A ⟶ κ` vanishes is itself zero.

This is `Stacks.NormalLocalDomain.hom_residueFieldShift_eq_zero_of_comp_mkQ_eq_zero` at `K`,
whose two hypotheses on `K` are supplied by `IsDerivedPushforwardStructureSheaf.isGE_zero` and
`IsDerivedPushforwardStructureSheaf.nonempty_homologyZeroIsoBase`; the dimension hypothesis is
the two-dimensionality of `A` in Situation 0AX8.

What is left of `ExtensionClassOfDerivedHom` is the vanishing of that precomposition. -/
theorem hom_residueFieldShift_eq_zero_of_comp_mkQ_eq_zero (V : VanishingSituation.{u})
    {K : DerivedCategory (ModuleCat.{u} V.A)}
    (hK : IsDerivedPushforwardStructureSheaf V.X V.f K)
    (α : V.residueFieldShift ⟶ K)
    (hα : ((DerivedCategory.singleFunctor (ModuleCat.{u} V.A) 0).map
      (ModuleCat.ofHom (IsLocalRing.maximalIdeal V.A).mkQ))⟦(-1 : ℤ)⟧' ≫ α = 0) :
    α = 0 := by
  have hd : 1 < ringKrullDim V.A := by rw [V.dimension_two]; norm_num
  have := hK.isGE_zero
  exact Stacks.NormalLocalDomain.hom_residueFieldShift_eq_zero_of_comp_mkQ_eq_zero hd K
    (hK.nonempty_homologyZeroIsoBase V.modification).some α hα

end VanishingSituation

end AlgebraicGeometry

end
