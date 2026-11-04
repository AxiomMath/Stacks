module

public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.RingTheory.Support
public import StacksFrontier.RingTheory.LocalCohomology.DepthVanishing.Supported
public import StacksFrontier.RingTheory.LocalCohomology.DepthVanishing.TorsionAcyclic
public import StacksCore.Tactic.StacksAttribute

/-!
# Local cohomology with support in `T` in degree zero

Degree-zero sections with support in a subset `T` of the prime spectrum form a *left exact*
functor on `A`-modules: a submodule of `M` is cut out by a condition on the annihilators of
individual elements, and that condition is insensitive to an injective change of ambient module.
Consequently the zeroth local cohomology module with support in `T` of a module placed in degree
zero is the module of its `T`-supported sections, and is in particular a submodule of `M`:

$$ H^0_T(M) \;=\; \Gamma_T(M) \;\subseteq\; M. $$

Over a Noetherian ring and for `M` finite this makes `H^0_T(M)` a finite module whose annihilator
`J` satisfies `V(J) ⊆ T`. That is exactly the base case `IH₀` of the double induction in the proof
of Faltings' annihilator theorem, Stacks 0EFC, which opens with the words *"the case `IH₀` is
trivial because `H^0_T(M)` is a submodule of `M` and hence finite and hence annihilated by some
ideal `J` with `V(J) ⊆ T`."*

Everything here is stated for the **set-indexed** model of local cohomology,
`Stacks.LocalCohomology.derivedSectionsWithSupportIn A T` and its cohomology modules
`Stacks.LocalCohomology.localCohomologyWithSupportIn A T`, which is the model in which Stacks
0EFC is phrased. No statement below mentions either the ideal-indexed derived torsion functor
`Stacks.Dualizing.derivedPowerTorsion` or the coreflection
`Stacks.Dualizing.localCohomologyFunctor`, and none should be read as a statement about them.

## Main results

* `Stacks.LocalCohomology.sectionsWithSupportInFunctor_preservesFiniteLimits` — **`Γ_T` is left
  exact.**
* `Stacks.LocalCohomology.nonempty_localCohomologyWithSupportIn_zero_iso` — **`H^0_T(M) = Γ_T(M)`**
  for an arbitrary `A`-module `M`, with no Noetherian hypothesis. This strengthens
  `Stacks.LocalCohomology.nonempty_localCohomologyWithSupportIn_zero_iso_of_injective`,
  which assumes `M` injective.
* `Stacks.LocalCohomology.finite_localCohomologyWithSupportIn_zero` — `H^0_T(M)` is a finite
  module when `A` is Noetherian and `M` is finite.
* `Stacks.LocalCohomology.exists_ideal_zeroLocus_subset_le_annihilator_localCohomology_of_le_zero`
  — the base case of Stacks 0EFC: for `M` finite over a Noetherian ring there is an ideal `J` with
  `V(J) ⊆ T` annihilating `H^i_T(M)` for every `i ≤ 0`.

## Implementation notes

Left exactness is checked through
`CategoryTheory.Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono`, so the whole content
is the elementwise statement that a `T`-supported section of the middle term
of a short exact sequence which dies in the right-hand term comes from a `T`-supported section of
the left-hand term. That in turn is `Stacks.LocalCohomology.torsionOf_eq_of_injective`: an
injective linear map does not change the annihilator of an element, so the membership criterion
`Stacks.LocalCohomology.mem_sectionsWithSupportIn_iff` transfers.

The degree-zero computation then runs on a bounded-below injective resolution `L` of `M`, which is
K-injective, so `H^0_T(M)` is the degree-zero homology of `Γ_T(L)`. Both `L` and `Γ_T(L)` vanish in
degree `-1`, so in both cases that homology is the cycles, i.e. the kernel of the differential out
of degree zero; and `Γ_T`, being left exact, carries the one kernel to the other. The cycles of `L`
in degree zero are `M` itself because `L` is a resolution. No naturality in `M` is asserted: the
statement is `Nonempty` of an isomorphism, which is all its consumers need and all that the
uniqueness-up-to-isomorphism of a limit cone point supplies.

No `@[stacks]` attribute is placed. Tag 0EFC is registered on exactly one statement, the full
annihilator criterion `exists_ideal_le_annihilator_localCohomology_iff`, and that statement is not
proved here — only its base case is. Tagging a fraction of a covering set would render the whole
tag as formalized.

## References

* [Stacks Project, Tag 0EFC](https://stacks.math.columbia.edu/tag/0EFC)
* [Stacks Project, Tag 0EF4](https://stacks.math.columbia.edu/tag/0EF4)
* [Stacks Project, Tag 0EEZ](https://stacks.math.columbia.edu/tag/0EEZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.LocalCohomology

variable {A : Type u} [CommRing A]

/-! ### Sections with support in `T` are left exact -/

/-- An injective linear map does not change the annihilator of an element. -/
theorem torsionOf_eq_of_injective {M N : Type*} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (f : M →ₗ[A] N) (hf : Function.Injective f) (x : M) :
    Ideal.torsionOf A N (f x) = Ideal.torsionOf A M x := by
  ext a
  rw [Ideal.mem_torsionOf_iff, Ideal.mem_torsionOf_iff, ← f.map_smul]
  exact ⟨fun h ↦ hf (by rw [h, map_zero]), fun h ↦ by rw [h, map_zero]⟩

/-- **Degree-zero sections with support in `T` are left exact.** Applied to a short exact
sequence, the functor `Γ_T` keeps the left-hand map injective and keeps the sequence exact at the
middle term: a `T`-supported section of `X₂` killed in `X₃` is the image of a unique section of
`X₁`, and that section is `T`-supported because an injective map preserves annihilators of
elements. -/
instance sectionsWithSupportInFunctor_preservesFiniteLimits (T : Set (PrimeSpectrum A)) :
    PreservesFiniteLimits (sectionsWithSupportInFunctor.{u, v} A T) := by
  rw [Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono]
  intro S hS
  have hf : Function.Injective S.f.hom := hS.moduleCat_injective_f
  refine ⟨?_, ?_⟩
  · rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      simp only [LinearMap.mem_ker]
      apply Subtype.ext
      change S.g.hom (S.f.hom x.val) = 0
      rw [← ModuleCat.comp_apply, S.zero]
      rfl
    · intro y hy
      simp only [LinearMap.mem_ker] at hy
      have hy0 : S.g.hom y.val = 0 := congrArg Subtype.val hy
      obtain ⟨x, hx⟩ : y.val ∈ LinearMap.range S.f.hom := by
        rw [hS.exact.moduleCat_range_eq_ker]; exact hy0
      have hmem : x ∈ sectionsWithSupportIn A T S.X₁ := by
        rw [mem_sectionsWithSupportIn_iff, ← torsionOf_eq_of_injective S.f.hom hf x, hx]
        exact (mem_sectionsWithSupportIn_iff A T _ y.val).mp y.property
      exact ⟨⟨x, hmem⟩, Subtype.ext hx⟩
  · rw [ModuleCat.mono_iff_injective]
    intro x y hxy
    exact Subtype.ext (hf (congrArg Subtype.val hxy))

/-- Sections with support in `T` commute with the degree-zero cycles of a cochain complex: both
are the kernel of the differential out of degree zero, and `Γ_T` preserves that kernel. -/
def sectionsWithSupportInObjCyclesIso (T : Set (PrimeSpectrum A))
    (L : CochainComplex (ModuleCat.{max u v} A) ℤ) :
    (sectionsWithSupportInFunctor.{u, v} A T).obj (HomologicalComplex.cycles L 0) ≅
      HomologicalComplex.cycles
        ((Functor.mapHomologicalComplex (sectionsWithSupportInFunctor.{u, v} A T)
          (ComplexShape.up ℤ)).obj L) 0 :=
  IsLimit.conePointUniqueUpToIso
    (KernelFork.mapIsLimit _ (L.cyclesIsKernel 0 1 (by simp))
      (sectionsWithSupportInFunctor.{u, v} A T))
    (((Functor.mapHomologicalComplex (sectionsWithSupportInFunctor.{u, v} A T)
      (ComplexShape.up ℤ)).obj L).cyclesIsKernel 0 1 (by simp))

/-! ### `H⁰_T(M) = Γ_T(M)` -/

/-- **`H^0_T(M) = Γ_T(M)` for an arbitrary `A`-module `M`.** The zeroth local cohomology module
with support in `T` of a module placed in degree zero is its module of `T`-supported sections. -/
theorem nonempty_localCohomologyWithSupportIn_zero_iso (T : Set (PrimeSpectrum A))
    (M : ModuleCat.{max u v} A) :
    Nonempty (localCohomologyWithSupportIn A T
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) 0 ≅
      (sectionsWithSupportInFunctor.{u, v} A T).obj M) := by
  have : EnoughInjectives (ModuleCat.{max u v} A) := ModuleCat.enoughInjectives A
  obtain ⟨L, q, hq, hinj, hGE⟩ :=
    CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective
      ((CochainComplex.singleFunctor (ModuleCat.{max u v} A) 0).obj M) 0
  have : L.IsKInjective := CochainComplex.isKInjective_of_injective L 0
  let e : DerivedCategory.Qh.obj ((HomotopyCategory.quotient (ModuleCat.{max u v} A)
      (ComplexShape.up ℤ)).obj L) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M :=
    (DerivedCategory.quotientCompQhIso (ModuleCat.{max u v} A)).app L ≪≫
      (asIso (DerivedCategory.Q.map q)).symm ≪≫
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{max u v} A) 0).app M).symm
  obtain ⟨iso⟩ := nonempty_localCohomology_iso_homology_of_isKInjective.{u, v} T _ 0 L e
  set C := (Functor.mapHomologicalComplex (sectionsWithSupportInFunctor.{u, v} A T)
    (ComplexShape.up ℤ)).obj L with hC
  have hLzero : IsZero (L.X (-1)) := L.isZero_of_isStrictlyGE 0 (-1) (by norm_num)
  have hCd : C.d (-1) 0 = 0 :=
    ((sectionsWithSupportInFunctor.{u, v} A T).map_isZero hLzero).eq_of_src _ _
  have hLd : L.d (-1) 0 = 0 := hLzero.eq_of_src _ _
  exact ⟨iso ≪≫ (C.isoHomologyπ (-1) 0 (by simp) hCd).symm ≪≫
    (sectionsWithSupportInObjCyclesIso.{u, v} T L).symm ≪≫
    (sectionsWithSupportInFunctor.{u, v} A T).mapIso
      (L.isoHomologyπ (-1) 0 (by simp) hLd ≪≫ (isoOfQuasiIsoAt q 0).symm ≪≫
        HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) (0 : ℤ) M)⟩

/-- `H^0_T(M)` is a finite module when `A` is Noetherian and `M` is finite: it is a submodule
of `M`. -/
theorem finite_localCohomologyWithSupportIn_zero [IsNoetherianRing A] (T : Set (PrimeSpectrum A))
    (M : Type (max u v)) [AddCommGroup M] [Module A M] [Module.Finite A M] :
    Module.Finite A ↥(localCohomologyWithSupportIn A T
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj (ModuleCat.of A M)) 0) := by
  obtain ⟨iso⟩ := nonempty_localCohomologyWithSupportIn_zero_iso.{u, v} T (ModuleCat.of A M)
  let e : ↥(sectionsWithSupportIn A T (ModuleCat.of A M)) ≃ₗ[A]
      ↥(localCohomologyWithSupportIn A T
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj (ModuleCat.of A M)) 0) :=
    iso.toLinearEquiv.symm
  exact Module.Finite.equiv e

/-- The annihilator of `H^0_T(M)` cuts out a closed subset of `T`, for `M` finite over a
Noetherian ring: `H^0_T(M)` is the finite module `Γ_T(M)`, whose support is contained in `T`. -/
theorem zeroLocus_annihilator_localCohomologyWithSupportIn_zero_subset [IsNoetherianRing A]
    (T : Set (PrimeSpectrum A)) (M : Type (max u v)) [AddCommGroup M] [Module A M]
    [Module.Finite A M] :
    PrimeSpectrum.zeroLocus
        ((Module.annihilator A ↥(localCohomologyWithSupportIn A T
          ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj
            (ModuleCat.of A M)) 0) : Ideal A) : Set A) ⊆ T := by
  obtain ⟨iso⟩ := nonempty_localCohomologyWithSupportIn_zero_iso.{u, v} T (ModuleCat.of A M)
  have hfin := finite_localCohomologyWithSupportIn_zero.{u, v} T M
  rw [← Module.support_eq_zeroLocus, iso.toLinearEquiv.support_eq]
  exact support_sectionsWithSupportIn_subset T (ModuleCat.of A M)

/-! ### The base case of Faltings' annihilator theorem -/

/-- **The base case of Stacks 0EFC.** For `M` a finite module over a Noetherian ring and `T` any
subset of the prime spectrum, a single ideal `J` with `V(J) ⊆ T` annihilates `H^i_T(M)` for every
`i ≤ 0`: the modules in negative degrees vanish, and `H^0_T(M) = Γ_T(M)` is a submodule of `M`,
hence finite, hence killed by its own annihilator, whose zero locus is its support and so lies
in `T`.

This is the induction hypothesis `IH₀` of the double induction proving the annihilator criterion
of Stacks 0EFC; it is not that criterion, and carries no Stacks attribute. Local cohomology here
is the set-indexed `Stacks.LocalCohomology.localCohomologyWithSupportIn`. -/
theorem exists_ideal_zeroLocus_subset_le_annihilator_localCohomology_of_le_zero
    [IsNoetherianRing A] (T : Set (PrimeSpectrum A))
    (M : Type (max u v)) [AddCommGroup M] [Module A M] [Module.Finite A M] :
    ∃ J : Ideal A, PrimeSpectrum.zeroLocus (J : Set A) ⊆ T ∧
      ∀ i : ℤ, i ≤ 0 →
        J ≤ Module.annihilator A ↥(localCohomologyWithSupportIn A T
          ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj
            (ModuleCat.of A M)) i) := by
  refine ⟨Module.annihilator A ↥(localCohomologyWithSupportIn A T
    ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj (ModuleCat.of A M)) 0),
    zeroLocus_annihilator_localCohomologyWithSupportIn_zero_subset.{u, v} T M, fun i hi ↦ ?_⟩
  rcases lt_or_eq_of_le hi with hi | rfl
  · have htop : Module.annihilator A ↥(localCohomologyWithSupportIn A T
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj
          (ModuleCat.of A M)) i) = ⊤ := by
      rw [Module.annihilator_eq_top_iff]
      exact ModuleCat.isZero_iff_subsingleton.mp
        (isZero_localCohomologyWithSupportIn_of_neg.{u, v} T (ModuleCat.of A M) i hi)
    rw [htop]
    exact le_top
  · exact le_rfl

end Stacks.LocalCohomology

end
