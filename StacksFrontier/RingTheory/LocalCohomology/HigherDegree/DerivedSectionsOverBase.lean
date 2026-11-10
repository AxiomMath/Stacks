module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.TotallyAcyclicGlobalSections
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.RingTheory.LocalCohomology.HigherDegree.CohomologyOverBase
public import StacksFrontier.RingTheory.LocalCohomology.HigherDegree.CohomologyOverBaseFunctor
public import StacksCore.Tactic.StacksAttribute

/-!
# Derived global sections of a scheme over a ring, as an object of the derived category

Let `A` be a commutative ring, let `f : V ⟶ Spec A` be a morphism of schemes and let `F` be a
sheaf of modules on `V`. Global sections of `F`, with scalars restricted to `A` along `f`, is the
additive functor `Stacks.LocalCohomology.sectionsOverBase` of
`StacksFrontier/RingTheory/LocalCohomology/HigherDegree/CohomologyOverBaseFunctor.lean`; this file
names its right derived functor on the bounded below derived category, viewed in the unbounded
derived category of `A`-modules.

That object is `RΓ(V, F)` as a complex of `A`-modules. Its degree-`p` cohomology is
`Stacks.LocalCohomology.cohomologyOverBase A f F p`, the `A`-module model of `H^p(V, F)`; it has
no cohomology in negative degrees; and as soon as the cohomology vanishes in all degrees above
some bound it is an object of the bounded above derived category `D⁻(A)`.

## Main definitions

* `Stacks.LocalCohomology.derivedSectionsOverBase` — `RΓ(V, F)` in `D(A)`.
* `Stacks.LocalCohomology.derivedSectionsMinus` — the same object in `D⁻(A)`, given a bound
  above which the cohomology vanishes.

## Main results

* `Stacks.LocalCohomology.nonempty_homology_derivedSectionsOverBase_iso`:
  `H^p(RΓ(V, F)) ≅ H^p(V, F)` as `A`-modules, for `p : ℕ`.
* `Stacks.LocalCohomology.isGE_derivedSectionsOverBase`: `RΓ(V, F)` has no cohomology in
  negative degrees.
* `Stacks.LocalCohomology.isLE_derivedSectionsOverBase`: if `H^n(V, F) = 0` for every natural
  number `n` above a bound `a`, then `RΓ(V, F)` lies in degrees `≤ a`.

## Implementation notes

`Stacks.LocalCohomology.cohomologyOverBase` is defined with Mathlib's `ℕ`-indexed right derived
functor `CategoryTheory.Functor.rightDerived`, computed on an injective resolution, while the
object of the derived category is produced by `CategoryTheory.Functor.rightDerivedFunctorPlus`.
The two indexings are compared by `Stacks.DerivedIndexing.rightDerivedIso`, and the restriction
of scalars is moved across the right derived functor by
`Stacks.LocalCohomology.cohomologyOverBaseIsoRightDerived`, which applies because restriction of
scalars is exact.

Everything here is at the module universe of the scheme, so
`Stacks.LocalCohomology.sectionsOverBase` and the comparison with
`Stacks.LocalCohomology.cohomologyOverBase` — both stated at an arbitrary module universe
`max u v` — are instantiated at `v := u`.

Vanishing in negative degrees is `Stacks.isGE_rightDerivedFunctorPlus_obj`, the part of
[Stacks, Tag 05TC] saying that a right derived functor moves cohomology to the right.

The bound above which the cohomology must vanish is an arbitrary integer, and the hypothesis is
imposed only at natural numbers, since `cohomologyOverBase` is indexed by `ℕ`; the negative
degrees are handled by the previous paragraph.

### The step of Tag 0ECC that this covers

This object is the complex called `RΓ(V, 𝒪_V)` in the proof of [Stacks, Tag 0ECC], for
`F = 𝒪_V`. The source applies the spectral sequence of More on Algebra, Example 15.63.4 to it,
which needs a bounded above complex of `A`-modules whose cohomology is `H^i(V, 𝒪_V)`; producing
that complex is the step formalized here, and
`Stacks.SpectralSequence.isZero_derivedTensorHomology_zero_singleHomology_zero` in
`StacksFrontier.Algebra.Homology.SpectralSequence.OriginVanishing` is the spectral-sequence step
that consumes it. The attribute on `Stacks.LocalCohomology.derivedSectionsMinus` is qualified
accordingly: it covers that step and no more.

What the proof of Tag 0ECC still needs beyond this is the vanishing
`RΓ(V, 𝒪_V) ⊗^L_A A/𝔪 = 0` — [Stacks, Tag 08IB] — and the vanishing of
`Tor_r^A(A/𝔪, H^{r-1}(V, 𝒪_V))` for `2 ≤ r < dim A` — [Stacks, Tag 0ECB] together with
[Stacks, Tag 0EBT]. None of those three tags is carried by the library.

## References

* [Stacks Project, Tag 05TC](https://stacks.math.columbia.edu/tag/05TC)
* [Stacks Project, Tag 0DWR](https://stacks.math.columbia.edu/tag/0DWR)
* [Stacks Project, Tag 0ECC](https://stacks.math.columbia.edu/tag/0ECC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.LocalCohomology

attribute [local instance] HasDerivedCategory.standard

variable (A : Type u) [CommRing A] {V : Scheme.{u}}

/-- Evaluation of a sheaf of modules at an open is additive. -/
instance evaluation_additive :
    (SheafOfModules.evaluation V.ringCatSheaf (op (⊤ : V.Opens))).Additive := by
  unfold SheafOfModules.evaluation
  infer_instance

/-- Restriction of scalars is exact, hence preserves homology. -/
instance restrictScalars_preservesHomology {R S : Type u} [Ring R] [Ring S] (φ : R →+* S) :
    (ModuleCat.restrictScalars.{u} φ).PreservesHomology :=
  ((Functor.exact_tfae (ModuleCat.restrictScalars.{u} φ)).out 2 3).mp fun _ hT ↦ by
    rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hT ⊢
    exact hT

/-- Global sections with scalars restricted to `A` is left exact: evaluation of a sheaf of
modules at an open preserves finite limits, and restriction of scalars is exact. -/
instance sectionsOverBase_preservesFiniteLimits (f : V ⟶ Spec (.of A)) :
    PreservesFiniteLimits (sectionsOverBase.{u, u} A f) := by
  let Ev : SheafOfModules.{u} V.ringCatSheaf ⥤ ModuleCat.{u} Γ(V, ⊤) :=
    SheafOfModules.evaluation V.ringCatSheaf (op (⊤ : V.Opens))
  let Re : ModuleCat.{u} Γ(V, ⊤) ⥤ ModuleCat.{u} A :=
    ModuleCat.restrictScalars (baseScalars A f)
  have hEv : PreservesFiniteLimits Ev := by
    change PreservesFiniteLimits (SheafOfModules.evaluation V.ringCatSheaf (op (⊤ : V.Opens)))
    infer_instance
  have hRe : PreservesFiniteLimits Re := by
    change PreservesFiniteLimits (ModuleCat.restrictScalars (baseScalars A f))
    infer_instance
  have hres : PreservesFiniteLimits (Ev ⋙ Re) := inferInstance
  exact hres

/-- `cohomologyOverBase` is the right derived functor of `sectionsOverBase`, up to moving the
restriction of scalars across the right derived functor. -/
theorem nonempty_cohomologyOverBase_iso_rightDerived
    (f : V ⟶ Spec (.of A)) (F : SheafOfModules.{u} V.ringCatSheaf) (p : ℕ) :
    Nonempty (cohomologyOverBase.{u, u} A f F p ≅
      ((sectionsOverBase.{u, u} A f).rightDerived p).obj F) :=
  ⟨cohomologyOverBaseIsoRightDerived.{u, u} A f F p⟩

/-- **`RΓ(V, F)` as an object of the derived category of `A`-modules.** The right derived
functor of global sections with scalars restricted to `A`, evaluated at `F` placed in degree
zero, viewed in the unbounded derived category. -/
def derivedSectionsOverBase (f : V ⟶ Spec (.of A))
    (F : SheafOfModules.{u} V.ringCatSheaf) : DerivedCategory (ModuleCat.{u} A) :=
  DerivedCategory.Plus.ι.obj ((sectionsOverBase.{u, u} A f).rightDerivedFunctorPlus.obj
    ((DerivedCategory.Plus.singleFunctor (SheafOfModules.{u} V.ringCatSheaf) 0).obj F))

/-- **The cohomology of `RΓ(V, F)` is the cohomology of `F` on `V`.** In degree `p : ℕ` the
cohomology of the derived global sections is the `A`-module `H^p(V, F)`. -/
theorem nonempty_homology_derivedSectionsOverBase_iso
    (f : V ⟶ Spec (.of A)) (F : SheafOfModules.{u} V.ringCatSheaf) (p : ℕ) :
    Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (p : ℤ)).obj
        (derivedSectionsOverBase A f F) ≅ cohomologyOverBase.{u, u} A f F p) := by
  obtain ⟨e⟩ := nonempty_cohomologyOverBase_iso_rightDerived A f F p
  refine ⟨?_ ≪≫ e.symm⟩
  exact ((Stacks.DerivedIndexing.rightDerivedIso (sectionsOverBase.{u, u} A f) p).app F).symm

/-- **`H⁰(V, F)` is the module of global sections of `F`.** Global sections with scalars
restricted to `A` is left exact, so its zeroth right derived functor is itself. -/
theorem nonempty_cohomologyOverBase_zero_iso_sections (f : V ⟶ Spec (.of A))
    (F : SheafOfModules.{u} V.ringCatSheaf) :
    Nonempty (cohomologyOverBase.{u, u} A f F 0 ≅ (sectionsOverBase.{u, u} A f).obj F) := by
  obtain ⟨e⟩ := nonempty_cohomologyOverBase_iso_rightDerived A f F 0
  exact ⟨e ≪≫ (Functor.rightDerivedZeroIsoSelf (sectionsOverBase.{u, u} A f)).app F⟩

/-- **The degree-zero cohomology of `RΓ(V, F)` is the module of global sections of `F`.** This
is the link to the last step of the proof of [Stacks, Tag 0ECC], whose hypothesis is about
`Γ(V, 𝒪_V)`. -/
theorem nonempty_homology_zero_derivedSectionsOverBase_iso_sections
    (f : V ⟶ Spec (.of A)) (F : SheafOfModules.{u} V.ringCatSheaf) :
    Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
      (derivedSectionsOverBase A f F) ≅ (sectionsOverBase.{u, u} A f).obj F) := by
  obtain ⟨e⟩ := nonempty_homology_derivedSectionsOverBase_iso A f F 0
  obtain ⟨e'⟩ := nonempty_cohomologyOverBase_zero_iso_sections A f F
  exact ⟨e ≪≫ e'⟩

/-- **`RΓ(V, F)` has no cohomology in negative degrees.** A right derived functor moves
cohomology to the right, and `F` is placed in degree zero. -/
instance isGE_derivedSectionsOverBase (f : V ⟶ Spec (.of A))
    (F : SheafOfModules.{u} V.ringCatSheaf) : (derivedSectionsOverBase A f F).IsGE 0 := by
  have h : ((sectionsOverBase.{u, u} A f).rightDerivedFunctorPlus.obj
      ((DerivedCategory.Plus.singleFunctor (SheafOfModules.{u} V.ringCatSheaf) 0).obj F)).IsGE 0 :=
    Functor.isGE_rightDerivedFunctorPlus_obj (F := sectionsOverBase.{u, u} A f) _ 0
  rw [← DerivedCategory.Plus.isGE_ι_obj_iff] at h
  exact h

/-- The cohomology of `RΓ(V, F)` vanishes in every negative degree. -/
theorem isZero_homology_derivedSectionsOverBase_of_neg (f : V ⟶ Spec (.of A))
    (F : SheafOfModules.{u} V.ringCatSheaf) (q : ℤ) (hq : q < 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) q).obj
      (derivedSectionsOverBase A f F)) :=
  DerivedCategory.isZero_of_isGE (derivedSectionsOverBase A f F) 0 q hq

/-- **`RΓ(V, F)` is bounded above as soon as the cohomology of `F` is.** If `H^n(V, F) = 0` for
every natural number `n` strictly above a bound `a`, then the derived global sections lie in
degrees `≤ a`: the negative degrees are covered by `isGE_derivedSectionsOverBase`. -/
theorem isLE_derivedSectionsOverBase (f : V ⟶ Spec (.of A))
    (F : SheafOfModules.{u} V.ringCatSheaf) (a : ℤ)
    (hvanish : ∀ n : ℕ, a < (n : ℤ) → IsZero (cohomologyOverBase.{u, u} A f F n)) :
    (derivedSectionsOverBase A f F).IsLE a := by
  rw [DerivedCategory.isLE_iff]
  intro i hi
  rcases lt_or_ge i 0 with hneg | hpos
  · exact isZero_homology_derivedSectionsOverBase_of_neg A f F i hneg
  · have hcast : ((i.toNat : ℕ) : ℤ) = i := Int.toNat_of_nonneg hpos
    obtain ⟨e⟩ := nonempty_homology_derivedSectionsOverBase_iso A f F i.toNat
    have hzero : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A)
        ((i.toNat : ℕ) : ℤ)).obj (derivedSectionsOverBase A f F)) :=
      IsZero.of_iso (hvanish i.toNat (by rw [hcast]; exact hi)) e
    rwa [hcast] at hzero

/-- **`RΓ(V, F)` as an object of the bounded above derived category `D⁻(A)`,** given a bound
above which the cohomology of `F` on `V` vanishes.

Together with `Stacks.LocalCohomology.nonempty_homology_derivedSectionsOverBase_iso` and
`Stacks.LocalCohomology.isGE_derivedSectionsOverBase` this is the complex `RΓ(V, 𝒪_V)` the proof
of [Stacks, Tag 0ECC] feeds to its spectral sequence: an object of `D⁻(A)` with no cohomology in
negative degrees whose cohomology in degree `p` is `H^p(V, 𝒪_V)`.

The attribute is qualified: this is the construction of that complex, not the whole tag. The
remaining steps need Tags 08IB, 0ECB and 0EBT, none of which the library carries; see the module
documentation. -/
@[stacks 0ECC "the complex RΓ(V, 𝒪_V) of A-modules, bounded above and concentrated in degrees ≥ 0"]
def derivedSectionsMinus (f : V ⟶ Spec (.of A))
    (F : SheafOfModules.{u} V.ringCatSheaf) (a : ℤ)
    (hvanish : ∀ n : ℕ, a < (n : ℤ) → IsZero (cohomologyOverBase.{u, u} A f F n)) :
    DerivedCategory.Minus (ModuleCat.{u} A) :=
  ⟨derivedSectionsOverBase A f F, ⟨a, isLE_derivedSectionsOverBase A f F a hvanish⟩⟩

/-- The underlying object of `Stacks.LocalCohomology.derivedSectionsMinus` in the unbounded
derived category is `Stacks.LocalCohomology.derivedSectionsOverBase`. -/
@[simp]
theorem derivedSectionsMinus_obj (f : V ⟶ Spec (.of A))
    (F : SheafOfModules.{u} V.ringCatSheaf) (a : ℤ)
    (hvanish : ∀ n : ℕ, a < (n : ℤ) → IsZero (cohomologyOverBase.{u, u} A f F n)) :
    (derivedSectionsMinus A f F a hvanish).1 = derivedSectionsOverBase A f F :=
  rfl

end Stacks.LocalCohomology

end
