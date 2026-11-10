module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveTopCohomologyExcision
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveTopCohomologyConstant
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CoverCompactificationBoundary
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CoverCompactificationGeometricCurve
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CoverDeckTwist
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicIntegralDirectImageCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.DimensionZeroWeights

/-!
# `H²_c` of the direct image of the constant sheaf along a geometrically irreducible cover

Let `U` be a curve over a finite field `k` with a compactification `j : U ⟶ Ū`, let `g : V ⟶ U`
be a connected finite étale cover with smooth projective compactification `V̄ ⟶ Ū`
(`AlgebraicGeometry.CoverCompactification`), and suppose `V` geometrically irreducible over `k`.
Then for `m` invertible in `k̄`

`H²_c(U_k̄, g_* ℤ/m) ≅ ℤ/m`:

`H²_c(U_k̄, g_* -) = H²_c(V_k̄, -)` along the finite `V̄ ⟶ Ū`
(`Stacks.EtaleCohomology.compactSupportSheafCohomologyIntegralIso`),
`H²_c(V_k̄, -) = H²(V̄_k̄, j_! -)`
(`Stacks.EtaleCohomology.compactSupportSheafCohomologyRestrictOpenIso`), `j_! j⁻¹ ℤ/m ⟶ ℤ/m` is an
isomorphism on `H²` since the boundary `V̄ ∖ V` is finite
(`Stacks.EtaleCohomology.bijective_compactSupportSheafCohomology_two_extensionByZero_counit`), and
`H²(V̄_k̄, ℤ/m) ≅ ℤ/m` for the smooth proper curve `V̄_k̄`
(`Stacks.EtaleCohomology.exists_addEquiv_compactSupportSheafCohomology_two_constant`).

This is the count `|H²_c(X_k̄, φ_* φ^* ℱ)| = |M|` for a geometrically connected Galois cover in the
proof of [Stacks, Tag 03VK].

The statement lives in the standard model `HasDerivedCategory.standard` of the derived category, in
which `Stacks.EtaleCohomology.compactSupportSheafCohomology` is defined.

## Main results

* `nonempty_linearEquiv_compactSupportSheafCohomology_two_directImage_constant`:
  `H²_c(U_k̄, g_* ℤ/m) ≅ ℤ/m` for a geometrically irreducible connected finite étale cover `g`.

## References

* [Stacks Project, Tag 03VK](https://stacks.math.columbia.edu/tag/03VK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

section Cover

attribute [local instance] HasDerivedCategory.standard

variable {k : Type u} [Field k] [Fintype k] {U V : Scheme.{u}} (fU : U ⟶ Spec (.of k))
  [LocallyOfFiniteType fU] [QuasiCompact fU] [IsSeparated fU] (j : CompactificationOf (Over.mk fU))
  (kbar : Type u) [Field kbar] [Algebra k kbar] [IsAlgClosed kbar] (m : ℕ) [NeZero m]
  (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)
  {g : V ⟶ U} [IsFinite g] [Etale g] [ConnectedSpace V]
  (C : CoverCompactification k j.toBase j.immersion g)

omit [LocallyOfFiniteType fU] [QuasiCompact fU] [IsSeparated fU] [IsFinite g] [Etale g] in
include hcard in
/-- **`H²_c(U_k̄, g_* ℤ/m) ≅ ℤ/m`** for a connected finite étale cover `g : V ⟶ U` with smooth
projective compactification `V̄` over `Ū`, `V` geometrically irreducible over `k` and `m`
invertible in `k̄`. -/
theorem nonempty_linearEquiv_compactSupportSheafCohomology_two_directImage_constant
    (hm : IsUnit (m : kbar)) (hgi : GeometricallyIrreducible (C.j ≫ C.q)) :
    Nonempty ((compactSupportSheafCohomology (ZMod m) fU j kbar 2).obj
        ((etaleModuleDirectImage.{u, 0} (ZMod m) g).obj
          (etaleModuleConstantSheaf (ZMod m) (ModuleCat.of (ZMod m) (ULift.{u + 1} (ZMod m)))
            V)) ≃ₗ[ZMod m] ZMod m) := by
  let Λ := ZMod m
  let M := ModuleCat.of Λ (ULift.{u + 1} Λ)
  let jO := (CompactificationOf.ofProper C.q).restrictOpen C.j
  have : IsIntegralHom (show jO.space ⟶ j.space from C.fb) :=
    ((IsFinite.iff_isIntegralHom_and_locallyOfFiniteType C.fb).1 C.isFinite).1
  have sq : IsPullback g jO.immersion j.immersion C.fb := by
    change IsPullback g (C.j ≫ 𝟙 C.Vb) j.immersion C.fb
    rw [Category.comp_id]
    exact C.isPullback.flip
  let α := compactSupportSheafCohomologyIntegralIso Λ fU j (C.j ≫ C.q) jO g C.fb C.hq sq kbar 2
  let β := compactSupportSheafCohomologyRestrictOpenIso Λ C.q (CompactificationOf.ofProper C.q)
    kbar 2 C.j
  let Lb := etaleModuleConstantSheaf Λ M C.Vb
  let G := (etaleModuleRestriction.{u, 0} Λ C.j).obj Lb
  let γ : G ≅ etaleModuleConstantSheaf Λ M V := restrictionConstantIso Λ M C.j
  have hc := bijective_compactSupportSheafCohomology_two_extensionByZero_counit C.q
    (CompactificationOf.ofProper C.q) kbar m C.boundaryι C.j C.range_j_eq_compl
    (topologicalKrullDim_le_zero_of_isFinite (C.boundaryι ≫ C.q)) Lb
  let e₁ : (compactSupportSheafCohomology Λ fU j kbar 2).obj
        ((etaleModuleDirectImage.{u, 0} Λ g).obj (etaleModuleConstantSheaf Λ M V)) ≅
      (compactSupportSheafCohomology Λ C.q (CompactificationOf.ofProper C.q) kbar 2).obj
        ((etaleModuleExtensionByZero.{u, 0} Λ C.j).obj G) :=
    (compactSupportSheafCohomology Λ fU j kbar 2).mapIso
        ((etaleModuleDirectImage.{u, 0} Λ g).mapIso γ.symm) ≪≫ (α.app G).symm ≪≫ β.app G
  let e₂ := LinearEquiv.ofBijective
    ((compactSupportSheafCohomology Λ C.q (CompactificationOf.ofProper C.q) kbar 2).map
      ((etaleModuleExtensionByZeroAdj.{u, 0} Λ C.j).counit.app Lb)).hom hc
  have := C.isCurve_fieldBaseChange kbar hgi
  have := C.smooth_fieldBaseChange kbar
  have := C.isProper_fieldBaseChange kbar
  obtain ⟨Φ, -⟩ :=
    exists_addEquiv_compactSupportSheafCohomology_two_constant C.q kbar p q hcard m hm
  exact ⟨(e₁.toLinearEquiv.trans e₂).trans
    { Φ with map_smul' := ZMod.map_smul Φ.toAddMonoidHom }⟩

end Cover

end Stacks.EtaleCohomology
