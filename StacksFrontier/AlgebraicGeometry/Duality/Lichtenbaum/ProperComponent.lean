module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCohomology.OverField
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Coherent
public import StacksFrontier.AlgebraicGeometry.Duality.ProperOverField.DualizingComplex
public import StacksFrontier.AlgebraicGeometry.ModuleGlobalSections
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Functoriality

/-!
# A proper top-dimensional component carries nonzero top cohomology

This is the implication (1) ⇒ (3) of [Stacks, Tag 0G5F], in contrapositive form. Let `X` be a
scheme locally of finite type over a field `k`. If an irreducible component `X' ⊂ X`, viewed as an
integral closed subscheme with its reduced induced structure, is proper over `k` and has dimension
`d`, then `H^d(X, i_* ω_{X'}) ≠ 0`, where `ω_{X'}` is the dualizing module of `X'` of
[Stacks, Tag 0FVV] and `i : X' ⟶ X` is the closed immersion; `i_* ω_{X'}` is coherent. Hence if
`H^d(X, F) = 0` for every coherent `F`, no irreducible component of dimension `d` is proper.

## Main results

* `Stacks.Duality.nontrivial_cohomologyOverField_relativeDualizingModule_of_isProper`: for `X`
  irreducible and proper over `k`, `H^{dim X}(X, ω_X) ≠ 0`.
* `Stacks.Duality.nontrivial_cohomologyOverField_pushforward_relativeDualizingModule`: the same
  pushed forward along a closed immersion.
* `Stacks.Duality.not_isProper_irreducibleComponent_of_forall_subsingleton_cohomologyOverField`:
  **(1) ⇒ (3) of [Stacks, Tag 0G5F]**, with `H^d(X, -)` the `k`-vector space
  `AlgebraicGeometry.cohomologyOverField`.
* `Stacks.Duality.not_isProper_irreducibleComponent_of_forall_isZero_rightDerived`: the same with
  `H^d(X, -)` the `Γ(X, 𝒪_X)`-module `((moduleGlobalSections X).rightDerived d).obj`, of which
  `AlgebraicGeometry.cohomologyOverField` is the restriction of scalars to `k`.

## Implementation notes

Cohomology is `AlgebraicGeometry.cohomologyOverField`, the functor in which part (6) of
[Stacks, Tag 0FVV] (`Stacks.Duality.dualizingModuleHomEquivOfIsProper`) is stated; vanishing is
`Subsingleton`. The irreducible component `Z` carries the reduced induced structure
`(Scheme.IdealSheafData.vanishingIdeal Z).subscheme`. The source deduces `H^d(X', ω_{X'}) ≠ 0`
from its duality with `H^0(X', 𝒪_{X'})`; here part (6) is applied to `F = ω_{X'}` itself: the
dual of `H^d(X', ω_{X'})` is `Hom(ω_{X'}, ω_{X'})`, which contains the identity, nonzero because
`ω_{X'}` has nonempty support by part (2).

None of the hypotheses "nonempty", "separated" or "quasi-compact" of [Stacks, Tag 0G5F] is used
in this direction, and `d` need not be `dim X`.

## References

* [Stacks Project, Tag 0G5F](https://stacks.math.columbia.edu/tag/0G5F)
* [Stacks Project, Tag 0FVV](https://stacks.math.columbia.edu/tag/0FVV)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Duality

variable {k : Type u} [Field k]

/-- **The dualizing module of an irreducible proper scheme over a field is nonzero.** By part (2)
of [Stacks, Tag 0FVV] its support is the union of the irreducible components of maximal
dimension, which for an irreducible scheme is everything. -/
theorem not_isZero_relativeDualizingModule_of_isProper {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] [IrreducibleSpace X] :
    ¬ IsZero (relativeDualizingModule f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
        (DerivedPushforward.derivedStructureSheaf (Spec (.of k)))) := by
  intro hM
  have hSupp := (relativeDualizingModule_of_isProper f).2.2
  rw [_root_.SheafOfModules.supp_eq_empty_of_isZero hM] at hSupp
  have hComp : (Set.univ : Set X) ∈ irreducibleComponents X := by
    rw [irreducibleComponents_eq_singleton]
    exact Set.mem_singleton _
  have hUniv : topologicalKrullDim (Set.univ : Set X) = topologicalKrullDim X :=
    IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ X).isHomeomorph
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  have hx : x ∈ ⋃₀ {C ∈ irreducibleComponents X |
      topologicalKrullDim C = topologicalKrullDim X} :=
    Set.mem_sUnion.mpr ⟨Set.univ, ⟨hComp, hUniv⟩, Set.mem_univ x⟩
  rw [← hSupp] at hx
  exact Set.notMem_empty x hx

/-- **`H^{dim X}(X, ω_X) ≠ 0` for `X` irreducible and proper over a field.** By part (6) of
[Stacks, Tag 0FVV] the `k`-dual of `H^{dim X}(X, ω_X)` is `Hom(ω_X, ω_X)`, which contains the
identity of the nonzero module `ω_X`. -/
theorem nontrivial_cohomologyOverField_relativeDualizingModule_of_isProper {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] [IrreducibleSpace X] :
    Nontrivial (cohomologyOverField k f
      (relativeDualizingModule f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
        (DerivedPushforward.derivedStructureSheaf (Spec (.of k))))
      (ENat.toNat ((topologicalKrullDim X).getD 0))) := by
  let M := relativeDualizingModule f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
    (DerivedPushforward.derivedStructureSheaf (Spec (.of k)))
  have : M.IsQuasicoherent := isQuasicoherent_relativeDualizingModule f _ _
  let := Scheme.linearOver f
  rw [← not_subsingleton_iff_nontrivial]
  intro hH
  have hDual : Subsingleton (cohomologyOverField k f M
      (ENat.toNat ((topologicalKrullDim X).getD 0)) →ₗ[k] k) :=
    ⟨fun a b ↦ LinearMap.ext fun x ↦ by rw [Subsingleton.elim x 0, map_zero, map_zero]⟩
  have hId : (𝟙 M : M ⟶ M) = 0 :=
    (dualizingModuleHomEquivOfIsProper f M).injective (hDual.elim _ _)
  exact not_isZero_relativeDualizingModule_of_isProper f ((IsZero.iff_id_eq_zero M).mpr hId)

/-- **Pushing the dualizing module forward from a proper irreducible closed subscheme.** Let
`i : Z ⟶ X` be a closed immersion with `Z` irreducible, `f : X ⟶ Spec k`, and `i ≫ f` proper.
Then `H^d(X, i_* ω_Z) ≠ 0` for `d = dim Z`, where `ω_Z` is the dualizing module of
[Stacks, Tag 0FVV]. -/
theorem nontrivial_cohomologyOverField_pushforward_relativeDualizingModule {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (f : X ⟶ Spec (.of k)) [IsProper (i ≫ f)]
    [IrreducibleSpace Z] (d : ℕ) (hd : topologicalKrullDim Z = d) :
    Nontrivial (cohomologyOverField k f ((Scheme.Modules.pushforward i).obj
      (relativeDualizingModule (i ≫ f)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs (i ≫ f))
        (DerivedPushforward.derivedStructureSheaf (Spec (.of k))))) d) := by
  have hnat : ENat.toNat ((topologicalKrullDim Z).getD 0) = d := by rw [hd]; rfl
  have h := nontrivial_cohomologyOverField_relativeDualizingModule_of_isProper (i ≫ f)
  rw [hnat] at h
  exact (cohomologyOverFieldPushforwardIsoOfIsClosedImmersion k i f _ d).toLinearEquiv.toEquiv.symm
    |>.nontrivial

/-- **[Stacks, Tag 0G5F], (1) ⇒ (3).** Let `X` be a scheme locally of finite type over a field
`k`, with structure morphism `f`, and let `d : ℕ`. If `H^d(X, F) = 0` for every coherent
`𝒪_X`-module `F`, then no irreducible component `Z` of `X` of dimension `d` is proper over `k`;
here `Z` carries its reduced induced closed subscheme structure
`(Scheme.IdealSheafData.vanishingIdeal Z).subscheme`, "dimension `d`" is the topological Krull
dimension of that subscheme, and "proper over `k`" is properness of its structure morphism
`C.subschemeι ≫ f`.

The witness is `F = i_* ω_Z`, the pushforward of the dualizing module of [Stacks, Tag 0FVV]:
it is coherent, and `H^d(X, i_* ω_Z) = H^d(Z, ω_Z) ≠ 0`. -/
theorem not_isProper_irreducibleComponent_of_forall_subsingleton_cohomologyOverField
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (d : ℕ) (h : ∀ (F : X.Modules) [F.IsCoherent], Subsingleton (cohomologyOverField k f F d)) :
    ∀ Z : irreducibleComponents X,
      let C := Scheme.IdealSheafData.vanishingIdeal (X := X)
        ⟨Z.1, isClosed_of_mem_irreducibleComponents Z.1 Z.2⟩
      topologicalKrullDim C.subscheme = d → ¬ IsProper (C.subschemeι ≫ f) := by
  intro Z C hdim hproper
  have : IrreducibleSpace C.subscheme :=
    Scheme.IdealSheafData.irreducibleSpace_subscheme X C (by
      rw [Scheme.IdealSheafData.range_subschemeι_vanishingIdeal]
      exact Z.2.1)
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let M := relativeDualizingModule (C.subschemeι ≫ f)
    (isQuasicoherent_homology_derivedPushforward_of_qcqs (C.subschemeι ≫ f))
    (DerivedPushforward.derivedStructureSheaf (Spec (.of k)))
  have : M.IsCoherent := (relativeDualizingModule_of_isProper (C.subschemeι ≫ f)).1
  have : ((Scheme.Modules.pushforward C.subschemeι).obj M).IsCoherent :=
    isCoherent_pushforward_of_isClosedImmersion C.subschemeι M
  have hne := nontrivial_cohomologyOverField_pushforward_relativeDualizingModule
    C.subschemeι f d hdim
  exact not_subsingleton _ (h ((Scheme.Modules.pushforward C.subschemeι).obj M))

/-- **[Stacks, Tag 0G5F], (1) ⇒ (3), for the `Γ(X, 𝒪_X)`-module cohomology.** As
`not_isProper_irreducibleComponent_of_forall_subsingleton_cohomologyOverField`, with the vanishing
of `H^d(X, F)` stated as `IsZero (((moduleGlobalSections X).rightDerived d).obj F)`; the two agree
since `AlgebraicGeometry.cohomologyOverField` only restricts scalars to `k`. -/
theorem not_isProper_irreducibleComponent_of_forall_isZero_rightDerived
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (d : ℕ) (h : ∀ (F : X.Modules) [F.IsCoherent],
      IsZero (((moduleGlobalSections X).rightDerived d).obj F)) :
    ∀ Z : irreducibleComponents X,
      let C := Scheme.IdealSheafData.vanishingIdeal (X := X)
        ⟨Z.1, isClosed_of_mem_irreducibleComponents Z.1 Z.2⟩
      topologicalKrullDim C.subscheme = d → ¬ IsProper (C.subschemeι ≫ f) :=
  not_isProper_irreducibleComponent_of_forall_subsingleton_cohomologyOverField k f d
    fun F _ ↦ (ModuleCat.isZero_iff_subsingleton.mp (h F) :)

end Stacks.Duality
