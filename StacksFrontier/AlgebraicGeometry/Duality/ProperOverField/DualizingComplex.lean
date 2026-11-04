module

public import StacksFrontier.AlgebraicGeometry.Duality.ProperOverField.Basic
public import StacksFrontier.AlgebraicGeometry.Duality.ProperOverField.DualizingModule

/-!
# Duality for proper schemes over a field

Let `X` be a proper scheme over a field `k`, with structure morphism `f : X ⟶ Spec k`. The
dualizing complex of [Stacks, Tag 0FVV] is `ω_X^• = a(𝒪_{Spec k})`, the value on `𝒪_{Spec k}[0]` of
the right adjoint `a` of `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_{Spec k})` ([Stacks, Tag 0A9E]):
`Stacks.Duality.relativeDualizingComplex f _ (derivedStructureSheaf (Spec k))`. Its cohomology
sheaf `ω_X = H^{-dim X}(ω_X^•)` is `Stacks.Duality.relativeDualizingModule`.

## Main results

The numbered parts of [Stacks, Tag 0FVV]:

* `Stacks.Duality.isDualizingComplex_relativeDualizingComplex_of_isProper` — `ω_X^•` is a dualizing
  complex (the existence assertion).
* `Stacks.Duality.le_zero_and_le_dim_of_not_isZero_homology_of_isProper` — part (1).
* `Stacks.Duality.relativeDualizingModule_of_isProper` — part (2).
* `Stacks.Duality.topologicalKrullDim_supp_homology_le_of_isProper` — part (3).
* `Stacks.Duality.exists_nontrivial_stalk_homology_iff_depth_le_of_isProper` — part (4).
* Part (5) is `Stacks.Duality.dualityEquiv` and its companions
  (`StacksFrontier/AlgebraicGeometry/Duality/ProperOverField/Duality.lean`).
* `Stacks.Duality.dualizingModuleHomEquivOfIsProper` and its naturality — part (6).

## Implementation notes

The parts are deduced, as in the source, from two facts about `ω_X^•`: it is a dualizing complex,
and its derived stalks at the closed points are normalized dualizing complexes. Both are read off
the affine chart description of `f^!𝒪_{Spec k}` ([Stacks, Tag 0BV2],
`Stacks.Duality.upperShriekStructureSheafCharts`) by the ring-level [Stacks, Tag 0BZL] and
[Stacks, Tag 0E9N]; the dimension function of `ω_X^•` then vanishes at closed points, hence is
`x ↦ dim(closure {x})`, and [Stacks, Tag 0AWN]'s argument gives parts (1)–(3), while
[Stacks, Tag 0AWR] gives part (4). Part (6) is part (5) at `F[0]` together with part (1).

The stalk `H^i(ω_{X,x}^•)` of part (4) is written as the stalk at `x` of the cohomology sheaf
`H^i(ω_X^•)`; the stalk functor is exact, so the two agree. "`H^i ⊕ … ⊕ H^0` is nonzero" is
written as the existence of a nonzero summand.

## References

* [Stacks Project, Tag 0FVV](https://stacks.math.columbia.edu/tag/0FVV)
* [Stacks Project, Tag 0AWN](https://stacks.math.columbia.edu/tag/0AWN)
* [Stacks Project, Tag 0BV2](https://stacks.math.columbia.edu/tag/0BV2)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Duality

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]

/-- A scheme proper over a field is Noetherian. -/
private theorem isNoetherian_of_isProper_over_field (f : X ⟶ Spec (.of k)) [IsProper f] :
    IsNoetherian X :=
  have := LocallyOfFiniteType.isLocallyNoetherian f
  have := QuasiCompact.compactSpace_of_compactSpace f
  {}

/-- **[Stacks, Tag 0FVV], existence.** For `X` proper over a field `k`, the complex
`ω_X^• = a(𝒪_{Spec k})` is a dualizing complex on `X`. -/
@[stacks 0FVV "existence: ω_X^• = a(O_{Spec k}) is a dualizing complex"]
theorem isDualizingComplex_relativeDualizingComplex_of_isProper :
    letI := LocallyOfFiniteType.isLocallyNoetherian f
    IsDualizingComplex (relativeDualizingComplex f
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
      (DerivedPushforward.derivedStructureSheaf (Spec (.of k)))).obj :=
  have := isNoetherian_of_isProper_over_field f
  ProperOverField.isDualizingComplex_of_charts (ProperOverField.hasCharts f)

/-- **[Stacks, Tag 0FVV], part (1).** `H^i(ω_X^•)` is nonzero only for `i ∈ [-dim X, 0]`. -/
@[stacks 0FVV "part (1): H^i(ω_X^•) is nonzero only for i ∈ [-dim X, 0]"]
theorem le_zero_and_le_dim_of_not_isZero_homology_of_isProper (i : ℤ)
    (hi : ¬ Limits.IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj
      (relativeDualizingComplex f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
        (DerivedPushforward.derivedStructureSheaf (Spec (.of k)))).obj)) :
    i ≤ 0 ∧ (((-i).toNat : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim X :=
  have := isNoetherian_of_isProper_over_field f
  (ProperOverField.vanishing_and_support_of_charts (ProperOverField.hasCharts f)).1 i hi

/-- **[Stacks, Tag 0FVV], part (2).** `ω_X = H^{-dim X}(ω_X^•)` is a coherent module with property
`(S₂)` whose support is the union of the irreducible components of dimension `dim X`. -/
@[stacks 0FVV "part (2): ω_X is a coherent (S₂)-module supported on the components of dimension \
dim X"]
theorem relativeDualizingModule_of_isProper :
    (relativeDualizingModule f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
        (DerivedPushforward.derivedStructureSheaf (Spec (.of k)))).IsCoherent ∧
    SheafHasPropertySk X (relativeDualizingModule f
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
        (DerivedPushforward.derivedStructureSheaf (Spec (.of k)))) 2 ∧
    _root_.SheafOfModules.supp (relativeDualizingModule f
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
        (DerivedPushforward.derivedStructureSheaf (Spec (.of k)))) =
      ⋃₀ {C ∈ irreducibleComponents X | topologicalKrullDim C = topologicalKrullDim X} :=
  have := isNoetherian_of_isProper_over_field f
  (ProperOverField.vanishing_and_support_of_charts (ProperOverField.hasCharts f)).2.2

/-- **[Stacks, Tag 0FVV], part (3).** The support of `H^i(ω_X^•)` has dimension at most `-i`
(and is empty for `i > 0`). -/
@[stacks 0FVV "part (3): dim Supp H^i(ω_X^•) ≤ -i"]
theorem topologicalKrullDim_supp_homology_le_of_isProper (i : ℤ) :
    topologicalKrullDim (_root_.SheafOfModules.supp
        ((DerivedCategory.homologyFunctor X.Modules i).obj
          (relativeDualizingComplex f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
            (DerivedPushforward.derivedStructureSheaf (Spec (.of k)))).obj)) ≤
      if i ≤ 0 then (((-i).toNat : ℕ) : WithBot ℕ∞) else ⊥ :=
  have := isNoetherian_of_isProper_over_field f
  (ProperOverField.vanishing_and_support_of_charts (ProperOverField.hasCharts f)).2.1 i

/-- **[Stacks, Tag 0FVV], part (4).** For `x ∈ X` closed, one of `H^i(ω_{X,x}^•)`, …,
`H^0(ω_{X,x}^•)` is nonzero if and only if `depth(𝒪_{X,x}) ≤ -i`. -/
@[stacks 0FVV "part (4): H^i(ω_{X,x}^•) ⊕ … ⊕ H^0(ω_{X,x}^•) ≠ 0 iff depth(O_{X,x}) ≤ -i, at \
closed points"]
theorem exists_nontrivial_stalk_homology_iff_depth_le_of_isProper {x : X}
    (hx : IsClosed ({x} : Set X)) (i : ℤ) :
    (∃ j : ℤ, i ≤ j ∧ j ≤ 0 ∧ Nontrivial (moduleStalkAtPoint
        ((DerivedCategory.homologyFunctor X.Modules j).obj
          (relativeDualizingComplex f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
            (DerivedPushforward.derivedStructureSheaf (Spec (.of k)))).obj) x)) ↔
      i ≤ 0 ∧ Module.depth (X.presheaf.stalk x) (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (X.presheaf.stalk x) ≤ ((-i).toNat : ℕ∞) :=
  have := isNoetherian_of_isProper_over_field f
  ProperOverField.exists_nontrivial_iff_depth_le_of_charts (ProperOverField.hasCharts f) hx i

/-- The cohomology sheaves of `ω_X^•` vanish below degree `-dim X` (part (1)). -/
theorem isZero_homology_of_lt_of_isProper :
    ∀ j < -(ENat.toNat ((topologicalKrullDim X).getD 0) : ℤ),
      Limits.IsZero ((DerivedCategory.homologyFunctor X.Modules j).obj
        (relativeDualizingComplex f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
          (DerivedPushforward.derivedStructureSheaf (Spec (.of k)))).obj) :=
  have := isNoetherian_of_isProper_over_field f
  ProperOverField.isZero_homology_of_lt_of_charts (ProperOverField.hasCharts f)

/-- **[Stacks, Tag 0FVV], part (6).** For `F` quasi-coherent on `X` there is a `k`-linear
isomorphism `Hom_X(F, ω_X) ≅ Hom_k(H^{dim X}(X, F), k)`, natural in `F`
(`Stacks.Duality.dualizingModuleHomEquivOfIsProper_comp`). -/
@[stacks 0FVV "part (6): Hom(F, ω_X) = Hom_k(H^{dim X}(X, F), k) for F quasi-coherent"]
def dualizingModuleHomEquivOfIsProper (F : X.Modules) [F.IsQuasicoherent] :
    letI := Scheme.linearOver f
    (F ⟶ relativeDualizingModule f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
        (DerivedPushforward.derivedStructureSheaf (Spec (CommRingCat.of k)))) ≃ₗ[k]
      (cohomologyOverField k f F (ENat.toNat ((topologicalKrullDim X).getD 0)) →ₗ[k] k) :=
  dualizingModuleHomEquiv f (isZero_homology_of_lt_of_isProper f) F

/-- **[Stacks, Tag 0FVV], part (6), functoriality.** The isomorphisms of part (6) are natural in
the quasi-coherent module `F`. -/
@[stacks 0FVV "part (6): the isomorphisms are functorial in F"]
theorem dualizingModuleHomEquivOfIsProper_comp {F G : X.Modules} [F.IsQuasicoherent]
    [G.IsQuasicoherent] (φ : F ⟶ G)
    (v : G ⟶ relativeDualizingModule f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
        (DerivedPushforward.derivedStructureSheaf (Spec (CommRingCat.of k))))
    (x : cohomologyOverField k f F (ENat.toNat ((topologicalKrullDim X).getD 0))) :
    letI := Scheme.linearOver f
    dualizingModuleHomEquivOfIsProper f F (φ ≫ v) x =
      dualizingModuleHomEquivOfIsProper f G v
        ((cohomologyOverFieldFunctor k f (ENat.toNat ((topologicalKrullDim X).getD 0))).map
          φ x) :=
  dualizingModuleHomEquiv_comp f (isZero_homology_of_lt_of_isProper f) φ v x

end Stacks.Duality

end
