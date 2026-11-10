module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveTopCohomologySmoothCompactification
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `H²_c` of a curve and of its smooth projective compactification, naturally

The isomorphism `H²_c(U_k̄, L|_U) ≅ H²(V̄_k̄, L)` of
`Stacks.EtaleCohomology.exists_linearEquiv_compactSupportSheafCohomology_two_coverCompactification`
can be chosen to carry `(a|_U)_*` to `a_*` for every endomorphism `a` of `L`.

## Main results

* `exists_linearEquiv_compactSupportSheafCohomology_two_coverCompactification_natural`.
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
/-- **`H²_c(U_k̄, L|_U) ≅ H²(V̄_k̄, L)`, compatibly with `π^*` and naturally in `L`**, for the
smooth projective compactification `j' : U ⟶ V̄` of a smooth connected curve `U` over a finite
field. -/
@[sga "4 XVIII 1.1.3" "(1.1.3.1), special case", sga "4½ Arcata 6.2.1" "Comparison clause H_c²(X"]
theorem exists_linearEquiv_compactSupportSheafCohomology_two_coverCompactification_natural
    (L : EtaleModules.{u, 0} (ZMod m) C.Vb) :
    ∃ e : (compactSupportSheafCohomology (ZMod m) fU j kbar 2).obj
        ((etaleModuleRestriction.{u, 0} (ZMod m) C.j).obj L) ≃ₗ[ZMod m]
        (compactSupportSheafCohomology (ZMod m) C.q (CompactificationOf.ofProper C.q) kbar 2).obj L,
      (∀ t, e (((compactSupportSheafFrobenius (ZMod m) fU j kbar p q hcard 2).app
          ((etaleModuleRestriction.{u, 0} (ZMod m) C.j).obj L)).hom t) =
        ((compactSupportSheafFrobenius (ZMod m) C.q (CompactificationOf.ofProper C.q) kbar p q
          hcard 2).app L).hom (e t)) ∧
      ∀ (a : L ⟶ L) t, e (((compactSupportSheafCohomology (ZMod m) fU j kbar 2).map
          ((etaleModuleRestriction.{u, 0} (ZMod m) C.j).map a)).hom t) =
        ((compactSupportSheafCohomology (ZMod m) C.q (CompactificationOf.ofProper C.q) kbar 2).map
          a).hom (e t) := by
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
  let TU := compactSupportSheafCohomology Λ fU j kbar 2
  let TV := compactSupportSheafCohomology Λ C.q (CompactificationOf.ofProper C.q) kbar 2
  let ι := TU.mapIso
    ((etaleModuleDirectImageIdIso Λ U).app G)
  let c := (etaleModuleExtensionByZeroAdj.{u, 0} Λ C.j).counit.app L
  have hZ : topologicalKrullDim C.boundary ≤ 0 :=
    topologicalKrullDim_le_zero_of_isFinite (C.boundaryι ≫ C.q)
  have hc := bijective_compactSupportSheafCohomology_two_extensionByZero_counit C.q
    (CompactificationOf.ofProper C.q) kbar m C.boundaryι C.j C.range_j_eq_compl hZ L
  let e₁ : TU.obj G ≅ TV.obj ((etaleModuleExtensionByZero.{u, 0} Λ C.j).obj G) :=
    ι.symm ≪≫ (α.app G).symm ≪≫ β.app G
  let e₃ := LinearEquiv.ofBijective (TV.map c).hom hc
  refine ⟨e₁.toLinearEquiv.trans e₃, fun t => ?_, fun a t => ?_⟩
  swap
  · let b := (etaleModuleRestriction.{u, 0} Λ C.j).map a
    have h₁ : TU.map b ≫ TU.map ((etaleModuleDirectImageIdIso Λ U).inv.app G) =
        TU.map ((etaleModuleDirectImageIdIso Λ U).inv.app G) ≫
          TU.map ((etaleModuleDirectImage.{u, 0} Λ (𝟙 U)).map b) := by
      rw [← TU.map_comp, ← TU.map_comp]
      exact congrArg TU.map ((etaleModuleDirectImageIdIso Λ U).inv.naturality b)
    let TO := compactSupportSheafCohomology Λ (C.j ≫ C.q) jO kbar 2
    have h₂ : TU.map ((etaleModuleDirectImage.{u, 0} Λ (𝟙 U)).map b) ≫ α.inv.app G =
        α.inv.app G ≫ TO.map b := α.inv.naturality b
    have h₃ : TO.map b ≫ β.hom.app G =
        β.hom.app G ≫ TV.map ((etaleModuleExtensionByZero.{u, 0} Λ C.j).map b) :=
      β.hom.naturality b
    have h₄ : TV.map ((etaleModuleExtensionByZero.{u, 0} Λ C.j).map b) ≫ TV.map c =
        TV.map c ≫ TV.map a := by
      rw [← TV.map_comp, ← TV.map_comp]
      exact congrArg TV.map ((etaleModuleExtensionByZeroAdj.{u, 0} Λ C.j).counit.naturality a)
    have hall : TU.map b ≫ e₁.hom ≫ TV.map c = e₁.hom ≫ TV.map c ≫ TV.map a := by
      simp only [e₁, ι, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv, Iso.app_inv, Iso.app_hom,
        Category.assoc]
      rw [reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₃, h₄]
    exact congrArg (fun φ => φ.hom t) hall
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
  have h₄ : TV.map c ≫ πV.app L =
      πV.app ((etaleModuleExtensionByZero.{u, 0} Λ C.j).obj G) ≫ TV.map c := πV.naturality c
  have hall : e₁.hom ≫ TV.map c ≫ πV.app L = πU.app G ≫ e₁.hom ≫ TV.map c := by
    simp only [e₁, Iso.trans_hom, Iso.symm_hom, Category.assoc]
    rw [h₄, reassoc_of% h₃, reassoc_of% h₂, reassoc_of% h₁]
  exact (congrArg (fun φ => φ.hom t) hall).symm

end Stacks.EtaleCohomology

end
