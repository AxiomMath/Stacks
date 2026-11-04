module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.Algebra.Homology.Double
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# The homology of a complex concentrated in two adjacent degrees

Let `c : ComplexShape ι`, let `i₀ ≠ i₁` be indices with `c.Rel i₀ i₁`, and let `f : X₀ ⟶ X₁`.
Mathlib's `HomologicalComplex.double f hi₀₁` is the complex with `X₀` in degree `i₀`, `X₁` in
degree `i₁`, `f` as its only differential and zero everywhere else.  Its homology is therefore
as simple as it could be:

* in degree `i₀` nothing maps *in*, so the homology is the **kernel** of `f`;
* in degree `i₁` nothing maps *out*, so the homology is the **cokernel** of `f`.

Mathlib states neither.  This file supplies both, together with the `ModuleCat` form in which
the two homology objects become `LinearMap.ker φ` and `N ⧸ LinearMap.range φ`.

The intended use is a two-term complex of modules presented as a `double`, for instance the
naive cotangent complex `Algebra.naiveCotangentComplex R S` of
`StacksFrontier/RingTheory/NaiveCotangent/Defs.lean`, whose degrees are `i₀ = 1` and `i₁ = 0` in
`ComplexShape.down ℕ`: there `homology 1` is `H₁(L_{S/R})` and `homology 0` is `Ω_{S/R}`, and
the two results below are what turns a statement about `(…).homology 1` or `(…).homology 0`
into a statement about the kernel and the cokernel of `Algebra.Extension.cotangentComplex`.

## Main definitions

* `HomologicalComplex.doubleScIso₀`, `HomologicalComplex.doubleScIso₁`: the short complexes
  computing the homology of `double f hi₀₁` in degrees `i₀` and `i₁`, identified with
  `0 ⟶ X₀ ⟶ X₁` and `X₀ ⟶ X₁ ⟶ 0` respectively.

## Main results

* `HomologicalComplex.doubleHomologyIsoKernel`: `(double f hi₀₁).homology i₀ ≅ kernel f`.
* `HomologicalComplex.doubleHomologyIsoCokernel`: `(double f hi₀₁).homology i₁ ≅ cokernel f`.
* `doubleHomologyLinearEquivKer`, `doubleHomologyLinearEquivQuotient`: the same two
  statements for a linear map `φ : M →ₗ[R] N`, as linear equivalences onto
  `LinearMap.ker φ` and `N ⧸ LinearMap.range φ`.

## Implementation notes

The whole content is the pair of short-complex identifications.  The homology of `double f`
in degree `i₀` is computed by `(double f hi₀₁).sc i₀`, the short complex
`X_{c.prev i₀} ⟶ X_{i₀} ⟶ X_{c.next i₀}` of differentials; its first map is zero because the
only nonzero differential of a `double` has source `i₀`, and `i₀ ≠ i₁` keeps `c.prev i₀` from
being a second source.  Once that short complex is identified with `0 ⟶ X₀ ⟶ X₁`, Mathlib's
`ShortComplex.asIsoHomologyπ` and `ShortComplex.cyclesIsoKernel` finish, and dually in degree
`i₁`.

The two commutation squares are discharged by first unfolding
`HomologicalComplex.sc'` and `HomologicalComplex.shortComplexFunctor'` with `dsimp only`.
This is not cosmetic: `shortComplexFunctor'` is a plain definition, so a projection such as
`((double f hi₀₁).sc' (c.prev i₀) i₀ i₁).X₁` does not reduce to
`(double f hi₀₁).X (c.prev i₀)` at the transparency `rw` and `simp` use, and a goal mixing the
two spellings is reported as *not type-correct under the implicit transparency level* — so
`Category.id_comp` and `Category.assoc` fail to fire on it even though it prints as a triviality.
Unfolding the functor first puts the goal in a single spelling, with no transparency option.
-/

@[expose] public section

open CategoryTheory Category Limits

namespace HomologicalComplex

universe v u

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
  {X₀ X₁ : C} (f : X₀ ⟶ X₁) {ι : Type*} {c : ComplexShape ι}
  {i₀ i₁ : ι} (hi₀₁ : c.Rel i₀ i₁) (h : i₀ ≠ i₁)

/-- The short complex computing the homology of `double f hi₀₁` in degree `i₀` is
`0 ⟶ X₀ ⟶ X₁`: the differential out of `i₀` is `f`, and the differential into `i₀` is zero
because `i₀` is the source, not the target, of the only nonzero differential. -/
public noncomputable def doubleScIso₀ :
    (double f hi₀₁).sc i₀ ≅
      ShortComplex.mk (0 : (double f hi₀₁).X (c.prev i₀) ⟶ X₀) f zero_comp :=
  (double f hi₀₁).isoSc' (c.prev i₀) i₀ i₁ rfl (c.next_eq' hi₀₁) ≪≫
    ShortComplex.isoMk (Iso.refl _) (doubleXIso₀ f hi₀₁) (doubleXIso₁ f hi₀₁ h)
      (by dsimp only [sc', shortComplexFunctor']
          simp [double_d_eq_zero₁ f hi₀₁ (c.prev i₀) i₀ h])
      (by dsimp only [sc', shortComplexFunctor']
          simp [double_d f hi₀₁ h])

/-- The short complex computing the homology of `double f hi₀₁` in degree `i₁` is
`X₀ ⟶ X₁ ⟶ 0`: the differential into `i₁` is `f`, and the differential out of `i₁` is zero
because `i₁` is the target, not the source, of the only nonzero differential. -/
public noncomputable def doubleScIso₁ :
    (double f hi₀₁).sc i₁ ≅
      ShortComplex.mk f (0 : X₁ ⟶ (double f hi₀₁).X (c.next i₁)) comp_zero :=
  (double f hi₀₁).isoSc' i₀ i₁ (c.next i₁) (c.prev_eq' hi₀₁) rfl ≪≫
    ShortComplex.isoMk (doubleXIso₀ f hi₀₁) (doubleXIso₁ f hi₀₁ h) (Iso.refl _)
      (by dsimp only [sc', shortComplexFunctor']
          simp [double_d f hi₀₁ h])
      (by dsimp only [sc', shortComplexFunctor']
          simp [double_d_eq_zero₀ f hi₀₁ i₁ (c.next i₁) h.symm])

/-- **The homology of `double f hi₀₁` in degree `i₀` is the kernel of `f`.**  Degree `i₀`
carries the source of the only nonzero differential, so nothing maps into it and the cycles
are already the homology. -/
public noncomputable def doubleHomologyIsoKernel [CategoryWithHomology C] [HasKernel f] :
    (double f hi₀₁).homology i₀ ≅ kernel f :=
  ShortComplex.homologyMapIso (doubleScIso₀ f hi₀₁ h) ≪≫
    (ShortComplex.asIsoHomologyπ _ rfl).symm ≪≫ ShortComplex.cyclesIsoKernel _

/-- **The homology of `double f hi₀₁` in degree `i₁` is the cokernel of `f`.**  Degree `i₁`
carries the target of the only nonzero differential, so nothing maps out of it and the
opcycles are already the homology. -/
public noncomputable def doubleHomologyIsoCokernel [CategoryWithHomology C] [HasCokernel f] :
    (double f hi₀₁).homology i₁ ≅ cokernel f :=
  ShortComplex.homologyMapIso (doubleScIso₁ f hi₀₁ h) ≪≫
    ShortComplex.asIsoHomologyι _ rfl ≪≫ ShortComplex.opcyclesIsoCokernel _

end HomologicalComplex

/-! ## The two homology modules of a two-term complex of modules -/

section ModuleCat

open HomologicalComplex

universe w

variable {R : Type*} [Ring R] {M N : Type w} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] (φ : M →ₗ[R] N) {ι : Type*} {c : ComplexShape ι}
  {i₀ i₁ : ι} (hi₀₁ : c.Rel i₀ i₁) (h : i₀ ≠ i₁)

/-- **The homology in degree `i₀` of the two-term complex of `R`-modules given by
`φ : M →ₗ[R] N` is `LinearMap.ker φ`.** -/
public noncomputable def doubleHomologyLinearEquivKer :
    (double (ModuleCat.ofHom φ) hi₀₁).homology i₀ ≃ₗ[R] LinearMap.ker φ :=
  (doubleHomologyIsoKernel (ModuleCat.ofHom φ) hi₀₁ h ≪≫
    ModuleCat.kernelIsoKer (ModuleCat.ofHom φ)).toLinearEquiv

/-- **The homology in degree `i₁` of the two-term complex of `R`-modules given by
`φ : M →ₗ[R] N` is `N ⧸ LinearMap.range φ`.** -/
public noncomputable def doubleHomologyLinearEquivQuotient :
    (double (ModuleCat.ofHom φ) hi₀₁).homology i₁ ≃ₗ[R] N ⧸ LinearMap.range φ :=
  (doubleHomologyIsoCokernel (ModuleCat.ofHom φ) hi₀₁ h ≪≫
    ModuleCat.cokernelIsoRangeQuotient (ModuleCat.ofHom φ)).toLinearEquiv

end ModuleCat

end
