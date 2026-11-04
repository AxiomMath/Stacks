module

public import StacksFrontier.RingTheory.LocalCohomology.LongExactSequence.AllModules
public import StacksFrontier.RingTheory.LocalCohomology.LowDegree.CechSectionsComparison

/-!
# Derived sections on the complement of a zero locus in positive degrees

Let `I` be a finitely generated ideal of a commutative ring `A`, let `U = Spec A \ V(I)` and let
`M` be an `A`-module. The affine localization triangle
`RΓ_{V(I)}(M) ⟶ M ⟶ RΓ(U, M̃|U) ⟶ RΓ_{V(I)}(M)[1]`
places the middle term in degree zero, so above degree zero the third term carries no information
of its own: the connecting map of the homology sequence

`H^n(RΓ(U, M̃|U)) ⟶ H^{n+1}_{V(I)}(M)`

is an isomorphism for every `n ≥ 1`, for an arbitrary
`Stacks.LocalCohomology.LocalizationTriangleData`. Vanishing and finiteness statements for the
third term follow.

## Main definitions

* `Stacks.LocalCohomology.complementHomologyIsoLocalCohomologyModule` — **the higher comparison**
  `H^n(RΓ(U, M̃|U)) ≅ H^{n+1}_{V(I)}(M)` for `n ≥ 1`, for an arbitrary localization triangle.
* `Stacks.LocalCohomology.cechComplementHomologyIsoLocalCohomologyModule` — the same for the
  localization triangle that `Stacks.LocalCohomology.localizationTriangleData` supplies
  unconditionally, so with no hypothesis beyond finite generation of `I`.

## Main results

* `Stacks.LocalCohomology.isIso_homologySequenceδ_triangle` — the connecting map of the
  localization triangle is an isomorphism in degrees `≥ 1`.
* `Stacks.LocalCohomology.isZero_homology_complement_iff` — the third term of the triangle has
  vanishing degree-`n` cohomology, `n ≥ 1`, exactly when `H^{n+1}_{V(I)}(M)` vanishes.
* `Stacks.LocalCohomology.isZero_homology_complement_of_isLocalCohomologyBound` and
  `Stacks.LocalCohomology.isZero_homology_complement_of_cohomologicalDimension_le` — the vanishing
  that a bound on the local cohomology of `A` forces.
* `Stacks.LocalCohomology.isLocalCohomologyBound_iff_isZero_homology_complement` and
  `Stacks.LocalCohomology.cohomologicalDimension_le_iff_isZero_homology_complement` — the
  converse as well: for `d ≥ 1`, a vanishing bound `d` for the local cohomology of `A` is the
  same thing as the vanishing of the degree-`n` cohomology of the third term for every module
  and every `n ≥ d`. This is the triangle-level form of (1) ⟺ (3) of Stacks 0DX7.
* `Stacks.LocalCohomology.finite_homology_complement_iff` — finiteness of the degree-`n`
  cohomology of the third term, `n ≥ 1`, is finiteness of `H^{n+1}_{V(I)}(M)`.

## References

* [Stacks Project, Tag 0DWR](https://stacks.math.columbia.edu/tag/0DWR)
* [Stacks Project, Tag 0DX7](https://stacks.math.columbia.edu/tag/0DX7)
* [Stacks Project, Tag 0BK0](https://stacks.math.columbia.edu/tag/0BK0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

attribute [local instance] HasDerivedCategory.standard

universe v u

namespace Stacks.LocalCohomology

variable {A : Type u} [CommRing A] {I : Ideal A} {hI : I.FG}

section Triangle

variable (D : LocalizationTriangleData.{u, v} A I hI) (M : ModuleCat.{v} A)

/-- The middle term of the localization triangle is a module placed in degree zero, hence
concentrated in degrees `≤ 0`. -/
theorem isLE_triangle_obj₂ : DerivedCategory.IsLE (D.triangle M).obj₂ 0 :=
  inferInstanceAs (DerivedCategory.IsLE
    ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj M) 0)

/-- The middle term of the localization triangle has no cohomology in positive degrees: it is the
module `M` placed in degree zero. -/
theorem isZero_homology_triangle_obj₂ (n : ℤ) (hn : 0 < n) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) n).obj (D.triangle M).obj₂) :=
  have := isLE_triangle_obj₂ D M
  DerivedCategory.isZero_of_isLE _ 0 n hn

/-- **The connecting map of the localization triangle is an isomorphism above degree zero.**
For `n ≥ 1` the connecting map `H^n(RΓ(U, M̃|U)) ⟶ H^{n+1}_{V(I)}(M)` is an isomorphism. -/
theorem isIso_homologySequenceδ_triangle (n : ℤ) (hn : 1 ≤ n) :
    IsIso (DerivedCategory.HomologySequence.δ (D.triangle M) n (n + 1) rfl) := by
  have hT := D.distinguished M
  have hmono : Mono (DerivedCategory.HomologySequence.δ (D.triangle M) n (n + 1) rfl) :=
    (DerivedCategory.HomologySequence.exact₃ (D.triangle M) hT n (n + 1) rfl).mono_g
      ((isZero_homology_triangle_obj₂ D M n (by omega)).eq_of_src _ 0)
  have hepi : Epi (DerivedCategory.HomologySequence.δ (D.triangle M) n (n + 1) rfl) :=
    (DerivedCategory.HomologySequence.exact₁ (D.triangle M) hT n (n + 1) rfl).epi_f
      ((isZero_homology_triangle_obj₂ D M (n + 1) (by omega)).eq_of_tgt _ 0)
  exact isIso_of_mono_of_epi _

/-- **The higher comparison.** For `n ≥ 1` the degree-`n` cohomology of the third term
`RΓ(U, M̃|U)` of the localization triangle is the local cohomology module `H^{n+1}_{V(I)}(M)`,
through the connecting map of the triangle. -/
def complementHomologyIsoLocalCohomologyModule (n : ℤ) (hn : 1 ≤ n) :
    (DerivedCategory.homologyFunctor (ModuleCat.{v} A) n).obj (D.complement.obj M) ≅
      localCohomologyModule A I hI M (n + 1) :=
  @asIso _ _ _ _ (DerivedCategory.HomologySequence.δ (D.triangle M) n (n + 1) rfl)
    (isIso_homologySequenceδ_triangle D M n hn)

/-- The higher comparison is the connecting map of the localization triangle. -/
theorem complementHomologyIsoLocalCohomologyModule_hom (n : ℤ) (hn : 1 ≤ n) :
    (complementHomologyIsoLocalCohomologyModule D M n hn).hom =
      DerivedCategory.HomologySequence.δ (D.triangle M) n (n + 1) rfl :=
  rfl

/-- **Vanishing above degree zero.** For `n ≥ 1` the degree-`n` cohomology of `RΓ(U, M̃|U)`
vanishes exactly when `H^{n+1}_{V(I)}(M)` does. -/
theorem isZero_homology_complement_iff (n : ℤ) (hn : 1 ≤ n) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) n).obj (D.complement.obj M)) ↔
      IsZero (localCohomologyModule A I hI M (n + 1)) :=
  Iso.isZero_iff (complementHomologyIsoLocalCohomologyModule D M n hn)

/-- **Finiteness above degree zero.** For `n ≥ 1` the degree-`n` cohomology of `RΓ(U, M̃|U)` is a
finite `A`-module exactly when `H^{n+1}_{V(I)}(M)` is. -/
theorem finite_homology_complement_iff (n : ℤ) (hn : 1 ≤ n) :
    Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) n).obj
        (D.complement.obj M)) ↔
      Module.Finite A (localCohomologyModule A I hI M (n + 1)) :=
  Module.Finite.equiv_iff (complementHomologyIsoLocalCohomologyModule D M n hn).toLinearEquiv

end Triangle

/-! ### Vanishing forced by a bound on the local cohomology of the ring -/

section Bound

variable (D : LocalizationTriangleData.{u, max u v} A I hI) (M : ModuleCat.{max u v} A)

/-- **A vanishing bound for the local cohomology of `A` kills the cohomology of `RΓ(U, M̃|U)`
above degree zero.** If `H^i_{V(I)}(A) = 0` for every `i > d`, then the degree-`n` cohomology
of the third term of the localization triangle vanishes in every degree `n` with `1 ≤ n` and
`d ≤ n`. -/
theorem isZero_homology_complement_of_isLocalCohomologyBound (d : ℤ)
    (hd : IsLocalCohomologyBound A I hI d) (n : ℤ) (hn : 1 ≤ n) (hdn : d ≤ n) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) n).obj
      (D.complement.obj M)) :=
  (isZero_homology_complement_iff D M n hn).2
    (isZero_homology_localCohomology_of_isLocalCohomologyBound I hI d hd M (n + 1) (by omega))

/-- **Vanishing from the cohomological dimension of Stacks 0DX8.** If `cd(A, I) ≤ n` and
`n ≥ 1`, the degree-`n` cohomology of `RΓ(U, M̃|U)` vanishes. -/
theorem isZero_homology_complement_of_cohomologicalDimension_le (n : ℤ) (hn : 1 ≤ n)
    (hcd : cohomologicalDimension A I hI ≤ n) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) n).obj
      (D.complement.obj M)) :=
  isZero_homology_complement_of_isLocalCohomologyBound D M _
    (isLocalCohomologyBound_cohomologicalDimension A I hI) n hn hcd

/-- **A vanishing bound read off the complement.** Conversely, if the degree-`n` cohomology of
`RΓ(U, M̃|U)` vanishes for every module and every `n ≥ d`, with `d ≥ 1`, then `H^i_{V(I)}(A) = 0`
for every `i > d`. -/
theorem isLocalCohomologyBound_of_isZero_homology_complement (d : ℤ) (hd : 1 ≤ d)
    (h : ∀ (N : ModuleCat.{max u v} A) (n : ℤ), d ≤ n →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) n).obj
        (D.complement.obj N))) :
    IsLocalCohomologyBound A I hI d := by
  refine ⟨by omega, (isZero_homology_localCohomology_forall_iff I hI d).2 fun N i hi => ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n : ℤ, i = n + 1 := ⟨i - 1, by omega⟩
  exact (isZero_homology_complement_iff D N n (by omega)).1 (h N n (by omega))

/-- **The triangle-level form of (1) ⟺ (3) of Stacks 0DX7.** For `d ≥ 1`, the local cohomology of
`A` vanishes above degree `d` exactly when the degree-`n` cohomology of the third term of the
localization triangle vanishes for every module and every `n ≥ d`. -/
theorem isLocalCohomologyBound_iff_isZero_homology_complement (d : ℤ) (hd : 1 ≤ d) :
    IsLocalCohomologyBound A I hI d ↔
      ∀ (N : ModuleCat.{max u v} A) (n : ℤ), d ≤ n →
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) n).obj
          (D.complement.obj N)) :=
  ⟨fun hbound N n hn =>
    isZero_homology_complement_of_isLocalCohomologyBound D N d hbound n (by omega) hn,
   isLocalCohomologyBound_of_isZero_homology_complement D d hd⟩

/-- **The cohomological dimension of Stacks 0DX8, measured on the complement.** For `d ≥ 1` the
cohomological dimension of `I` is at most `d` exactly when the degree-`n` cohomology of
`RΓ(U, M̃|U)` vanishes for every module and every `n ≥ d`. -/
theorem cohomologicalDimension_le_iff_isZero_homology_complement (d : ℤ) (hd : 1 ≤ d) :
    cohomologicalDimension A I hI ≤ d ↔
      ∀ (N : ModuleCat.{max u v} A) (n : ℤ), d ≤ n →
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) n).obj
          (D.complement.obj N)) :=
  ⟨fun hcd N n hn =>
    isZero_homology_complement_of_cohomologicalDimension_le D N n (by omega) (by omega),
   fun h => cohomologicalDimension_le A I hI d
     (isLocalCohomologyBound_of_isZero_homology_complement D d hd h)⟩

end Bound

/-! ### The unconditional localization triangle -/

section Unconditional

variable (A) (I) (hI) in
/-- **The higher comparison for the localization triangle of Stacks 0DWR**, which
`Stacks.LocalCohomology.localizationTriangleData` provides for every finitely generated ideal:
for `n ≥ 1` the degree-`n` cohomology of its third term is `H^{n+1}_{V(I)}(M)`. -/
def cechComplementHomologyIsoLocalCohomologyModule (M : ModuleCat.{max u v} A) (n : ℤ)
    (hn : 1 ≤ n) :
    (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) n).obj
        ((localizationTriangleData.{v} A I hI).complement.obj M) ≅
      localCohomologyModule A I hI M (n + 1) :=
  complementHomologyIsoLocalCohomologyModule (localizationTriangleData.{v} A I hI) M n hn

variable (A) (I) (hI) in
/-- **Vanishing above degree zero for the unconditional localization triangle.** For a finitely
generated ideal of cohomological dimension at most `n`, with `n ≥ 1`, the degree-`n` cohomology
of the third term of the localization triangle vanishes, for every module. -/
theorem isZero_homology_cechComplement_of_cohomologicalDimension_le
    (M : ModuleCat.{max u v} A) (n : ℤ) (hn : 1 ≤ n)
    (hcd : cohomologicalDimension A I hI ≤ n) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) n).obj
      ((localizationTriangleData.{v} A I hI).complement.obj M)) :=
  isZero_homology_complement_of_cohomologicalDimension_le
    (localizationTriangleData.{v} A I hI) M n hn hcd

end Unconditional

end Stacks.LocalCohomology

end
