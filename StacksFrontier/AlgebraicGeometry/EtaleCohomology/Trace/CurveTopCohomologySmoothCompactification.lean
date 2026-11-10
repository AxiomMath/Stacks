module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveTopCohomologyExcision
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveCompactificationIndependence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CoverCompactificationBoundary
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.DimensionZeroWeights
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `H²_c` of a smooth curve is `H²` of its smooth projective compactification

Let `U` be a smooth connected curve over a finite field `k` with a compactification `j : U ⟶ Ū`
over `k`, and let `j' : U ⟶ V̄` be its smooth projective compactification over `Ū`
(`AlgebraicGeometry.CoverCompactification` for the identity of `U`). For every sheaf `L` of
`ℤ/m`-modules on `V̄_étale` and an algebraically closed extension `k̄` of `k`,

`H²_c(U_k̄, L|_U) ≅ H²(V̄_k̄, L)`,

compatibly with the canonical geometric Frobenius: `H²_c` through `j` and through `j'` agree
(`Stacks.EtaleCohomology.compactSupportSheafCohomologyIntegralIso` along the finite `V̄ ⟶ Ū`),
`H²_c(U_k̄, -) = H²(V̄_k̄, j'_! -)`
(`Stacks.EtaleCohomology.compactSupportSheafCohomologyRestrictOpenIso`), and `j'_! j'⁻¹ L ⟶ L`
induces an isomorphism on `H²` since the boundary `V̄ ∖ U` is finite
(`Stacks.EtaleCohomology.bijective_compactSupportSheafCohomology_two_extensionByZero_counit`).

## Main results

* `exists_linearEquiv_compactSupportSheafCohomology_two_coverCompactification`: the isomorphism
  `H²_c(U_k̄, L|_U) ≅ H²(V̄_k̄, L)`, compatible with the geometric Frobenius.

## References

* [Stacks Project, Tag 03VK](https://stacks.math.columbia.edu/tag/03VK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable {k : Type u} [Field k] [Fintype k] {U : Scheme.{u}} (fU : U ⟶ Spec (.of k))
  [IsCurve k fU] [Smooth fU] [LocallyOfFiniteType fU] [QuasiCompact fU] [IsSeparated fU]
  (j : CompactificationOf (Over.mk fU)) (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar] (m : ℕ) [NeZero m] (p q : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ q)
  (C : CoverCompactification k j.toBase j.immersion (𝟙 U))

omit [IsCurve k fU] [Smooth fU] [LocallyOfFiniteType fU] [QuasiCompact fU] [IsSeparated fU] in
/-- **`H²_c(U_k̄, L|_U) ≅ H²(V̄_k̄, L)`, compatibly with `π^*`**, for the smooth projective
compactification `j' : U ⟶ V̄` of a smooth connected curve `U` over a finite field. -/
@[sga "4 XVIII 1.1.3" "(1.1.3.1), special case", sga "4½ Arcata 6.2.1" "Comparison clause H_c²(X"]
theorem exists_linearEquiv_compactSupportSheafCohomology_two_coverCompactification
    (L : EtaleModules.{u, 0} (ZMod m) C.Vb) :
    ∃ e : (compactSupportSheafCohomology (ZMod m) fU j kbar 2).obj
        ((etaleModuleRestriction.{u, 0} (ZMod m) C.j).obj L) ≃ₗ[ZMod m]
        (compactSupportSheafCohomology (ZMod m) C.q (CompactificationOf.ofProper C.q) kbar 2).obj L,
      ∀ t, e (((compactSupportSheafFrobenius (ZMod m) fU j kbar p q hcard 2).app
          ((etaleModuleRestriction.{u, 0} (ZMod m) C.j).obj L)).hom t) =
        ((compactSupportSheafFrobenius (ZMod m) C.q (CompactificationOf.ofProper C.q) kbar p q
          hcard 2).app L).hom (e t) := by
  let Λ := ZMod m
  let jO := (CompactificationOf.ofProper C.q).restrictOpen C.j
  have : IsIntegralHom (show jO.space ⟶ j.space from C.fb) :=
    ((IsFinite.iff_isIntegralHom_and_locallyOfFiniteType C.fb).1 C.isFinite).1
  have hφb : C.fb ≫ j.toBase = jO.toBase := C.hq
  have sq : IsPullback (𝟙 U) jO.immersion j.immersion C.fb := by
    change IsPullback (𝟙 U) (C.j ≫ 𝟙 C.Vb) j.immersion C.fb
    rw [Category.comp_id]
    exact C.isPullback.flip
  let α := compactSupportSheafCohomologyIntegralIso Λ fU j (C.j ≫ C.q) jO (𝟙 U) C.fb hφb sq kbar 2
  let β := compactSupportSheafCohomologyRestrictOpenIso Λ C.q (CompactificationOf.ofProper C.q)
    kbar 2 C.j
  let G := (etaleModuleRestriction.{u, 0} Λ C.j).obj L
  let ι := (compactSupportSheafCohomology Λ fU j kbar 2).mapIso
    ((etaleModuleDirectImageIdIso Λ U).app G)
  let c := (etaleModuleExtensionByZeroAdj.{u, 0} Λ C.j).counit.app L
  have hc := bijective_compactSupportSheafCohomology_two_extensionByZero_counit C.q
    (CompactificationOf.ofProper C.q) kbar m C.boundaryι C.j C.range_j_eq_compl
    (topologicalKrullDim_le_zero_of_isFinite (C.boundaryι ≫ C.q)) L
  let e₁ : (compactSupportSheafCohomology Λ fU j kbar 2).obj G ≅
      (compactSupportSheafCohomology Λ C.q (CompactificationOf.ofProper C.q) kbar 2).obj
        ((etaleModuleExtensionByZero.{u, 0} Λ C.j).obj G) :=
    ι.symm ≪≫ (α.app G).symm ≪≫ β.app G
  let e₃ := LinearEquiv.ofBijective
    ((compactSupportSheafCohomology Λ C.q (CompactificationOf.ofProper C.q) kbar 2).map c).hom hc
  refine ⟨e₁.toLinearEquiv.trans e₃, fun t => ?_⟩
  let πU := compactSupportSheafFrobenius Λ fU j kbar p q hcard 2
  let πO := compactSupportSheafFrobenius Λ (C.j ≫ C.q) jO kbar p q hcard 2
  let πV := compactSupportSheafFrobenius Λ C.q (CompactificationOf.ofProper C.q) kbar p q hcard 2
  have h₁ : ι.inv ≫ πU.app _ = πU.app G ≫ ι.inv := πU.naturality _
  have h₂ : (α.app G).inv ≫ πO.app G = πU.app _ ≫ (α.app G).inv := by
    have h : πO.app G ≫ (α.app G).hom = (α.app G).hom ≫ πU.app _ := NatTrans.congr_app
      (compactSupportSheafCohomologyIntegralIso_hom_frobenius Λ fU j (C.j ≫ C.q) jO (𝟙 U) C.fb hφb
        sq kbar p q hcard 2) G
    rw [Iso.inv_comp_eq, ← reassoc_of% h, Iso.hom_inv_id, Category.comp_id]
  have h₃ : (β.app G).hom ≫ πV.app ((etaleModuleExtensionByZero.{u, 0} Λ C.j).obj G) =
      πO.app G ≫ (β.app G).hom := (NatTrans.congr_app
      (compactSupportSheafCohomologyRestrictOpenIso_hom_frobenius Λ C.q
        (CompactificationOf.ofProper C.q) kbar 2 C.j p q hcard) G).symm
  have h₄ : (compactSupportSheafCohomology Λ C.q (CompactificationOf.ofProper C.q) kbar 2).map c ≫
      πV.app L = πV.app ((etaleModuleExtensionByZero.{u, 0} Λ C.j).obj G) ≫
        (compactSupportSheafCohomology Λ C.q (CompactificationOf.ofProper C.q) kbar 2).map c :=
    πV.naturality c
  have hall : e₁.hom ≫ (compactSupportSheafCohomology Λ C.q (CompactificationOf.ofProper C.q)
      kbar 2).map c ≫ πV.app L = πU.app G ≫ e₁.hom ≫
        (compactSupportSheafCohomology Λ C.q (CompactificationOf.ofProper C.q) kbar 2).map c := by
    simp only [e₁, Iso.trans_hom, Iso.symm_hom, Category.assoc]
    rw [h₄, reassoc_of% h₃, reassoc_of% h₂, reassoc_of% h₁]
  exact (congrArg (fun φ => φ.hom t) hall).symm

end Stacks.EtaleCohomology

end
