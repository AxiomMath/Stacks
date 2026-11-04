module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicUpperVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportCompactificationIndependence

/-!
# `Hⁱ_c(X_k̄, G) = 0` above `2 dim X` for torsion sheaves of `Λ`-modules

Let `X` be separated of finite type over a finite field `k`, `k̄` an algebraically closed
extension of `k`, `Λ` a commutative ring and `G` a sheaf of `Λ`-modules on `X_étale` killed by a
positive integer `m`. Then `Hⁱ_c(X_k̄, G) = 0` for `i > 2 dim X`: the cohomology on the proper
scheme `X̄_k̄` of the torsion sheaf `(j_! G)|_{X̄_k̄}`, supported on `X_k̄`, vanishes above
`2 dim X_k̄` ([Stacks, Tag 095U]). This is, in the namespace `Stacks.EtaleCohomology`,
`isZero_compactSupportFrobeniusCohomologyGroup_single_of_topologicalKrullDim_le` for coefficients
other than `ℤ/mℤ`, e.g. `ℤ_ℓ` with `G` killed by a power of `ℓ`.

In dimension zero (`X = Spec κ` for a finite field `κ`) it says that `Hⁱ_c(Spec κ̄, G)` vanishes
for `i ≠ 0`, the input of the computation of the stalks of `Rʳ g_! G` at closed points in the
reduction of the weight bound of Weil II to curves
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)).

## Main results

* `Stacks.EtaleCohomology.isZero_compactSupportFrobeniusCohomologyGroup_single_of_nsmul_eq_zero`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [IsAlgClosed kbar]
  [Algebra k kbar]

omit [Fintype k] [IsSeparated f] in
/-- **`Hⁱ_c(X_k̄, G) = 0` for `i > 2 dim X`**, for every sheaf `G` of `Λ`-modules on `X_étale`
killed by a positive integer: the cohomology on the proper scheme `X̄_k̄` of the torsion sheaf
`(j_! G)|_{X̄_k̄}`, supported on `X_k̄`, vanishes above `2 dim X_k̄` by Tag 095U, and
`dim X_k̄ ≤ dim X`. -/
theorem isZero_compactSupportFrobeniusCohomologyGroup_single_of_nsmul_eq_zero
    (Λ : Type) [CommRing Λ] (G : EtaleModules.{u, 0} Λ X) (m : ℕ) (hm : 0 < m)
    (hG : m • 𝟙 G = 0) (d : ℕ) (hdim : topologicalKrullDim X ≤ d) (i : ℤ) (hi : 2 * (d : ℤ) < i) :
    IsZero (compactSupportFrobeniusCohomologyGroup.{u, 0} Λ f j kbar
      ⟨(CochainComplex.singleFunctor _ 0).obj G, CochainComplex.plus_singleFunctor_obj G⟩ i) := by
  obtain ⟨q', rfl⟩ : ∃ q' : ℕ, i = q' := ⟨i.toNat, by omega⟩
  refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctor _ (q' : ℤ)).mapIso
    (compactSupportFrobeniusCohomologySingleIso f j kbar G))
  refine isZero_homology_derivedDirectImageSections_of_subsingleton_sheafH Λ _ _ q' ?_
  have : QuasiCompact (compactificationFieldBaseChangeImmersion f j kbar ≫
      pullback.snd j.toBase (specAlgebraMap k kbar)) := by
    rw [compactificationFieldBaseChange_immersion_comp_snd]
    infer_instance
  have : QuasiCompact (compactificationFieldBaseChangeImmersion f j kbar) :=
    QuasiCompact.of_comp _ (pullback.snd j.toBase (specAlgebraMap k kbar))
  have hXk : topologicalKrullDim ↥(pullback f (specAlgebraMap k kbar) : Scheme.{u}) ≤ d :=
    topologicalKrullDim_pullback_le_of_fiber f d
      (fun y ↦ (topologicalKrullDim_fiber_of_spec_field k f y).le.trans hdim) _
  let T := etaleModuleExtensionByZero.{u, 0} Λ j.immersion ⋙
    etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk j.toBase) kbar)
  have hT : m • 𝟙 (T.obj G) = 0 := by
    rw [← T.map_id, ← Functor.map_nsmul, hG, Functor.map_zero]
  exact subsingleton_sheafH_of_isZero_etaleRestriction_of_disjoint
    (properSeparablyClosedSheafHVanishingStatement_of_properDirectImageVanishingStatement
      properDirectImageVanishingStatement) kbar
    (pullback.snd j.toBase (specAlgebraMap k kbar))
    (compactificationFieldBaseChangeImmersion f j kbar)
    d hXk ((etaleModuleUnderlyingAbelian _ Λ).obj (T.obj G))
    (isTorsionEtaleModule_of_nsmul_id_eq_zero_typeZero (T.obj G) m hm hT)
    (fun v _ hv ↦ isZero_etaleRestriction_underlyingAbelian_fieldBaseChange_extensionByZero f j
      kbar _ v hv) q' (by omega)

end Stacks.EtaleCohomology
