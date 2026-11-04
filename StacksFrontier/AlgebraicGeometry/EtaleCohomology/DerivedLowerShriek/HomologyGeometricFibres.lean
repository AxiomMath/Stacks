module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.LowerShriekHomologyBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.InverseImageFamilyVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EnoughGeometricPoints

/-!
# The vanishing of `H^q(Rf_! K)` is checked on the geometric fibres

Let `f : X ⟶ Y` be a morphism with a compactification `j`, and `K ∈ D⁺(X_étale, Λ)` killed by a
positive integer. For every point `y` of `Y`, let `ȳ : Spec Ω ⟶ Y` be the geometric point at an
algebraic closure `Ω` of `κ(y)` (`AlgebraicGeometry.GeometricPoint.ofPoint`). If
`H^q(Rf'_!(K|_{X_ȳ}))` vanishes on `Spec Ω` for every `y`, `f' : X_ȳ ⟶ Spec Ω` the fibre, then
`H^q(Rf_! K) = 0`: the inverse images along the `ȳ` detect vanishing
(`Stacks.EtaleCohomology.isZero_of_forall_isZero_etaleModuleInverseImage`), inverse image commutes
with cohomology sheaves, and `ȳ⁻¹ Rf_! K ≅ Rf'_! (K|_{X_ȳ})` by proper base change for `Rf_!` on
`D⁺_tors` ([Stacks, Tag 0F7L], `Stacks.EtaleCohomology.isIso_derivedLowerShriekBaseChange_app`).

This reduces the surjectivity of the Gysin map of the Leray step of the reduction of the weight
bound of Weil II to curves ([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)) to the geometric
fibres.

## Main results

* `Stacks.EtaleCohomology.isZero_homology_derivedLowerShriek_of_geometricFibres`.

## Implementation notes

`Stacks.EtaleCohomology.derivedLowerShriek` lives in the standard model
`HasDerivedCategory.standard`, and so does the statement here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-- The geometric points `AlgebraicGeometry.GeometricPoint.ofPoint`, at the points of a scheme,
cover it. -/
theorem iUnion_range_geometricPoint_ofPoint (Y : Scheme.{u}) :
    ⋃ y : Y, Set.range (GeometricPoint.ofPoint Y y).hom.base = Set.univ :=
  Set.eq_univ_of_forall fun y =>
    Set.mem_iUnion.2 ⟨y, default, GeometricPoint.ofPoint_liesOver Y y⟩

variable (Λ : Type) [Ring Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) (j : CompactificationOf (Over.mk f))

/-- **`H^q(Rf_! K) = 0` as soon as it vanishes on every geometric fibre** at the algebraic
closures of the residue fields, for `K` killed by a positive integer: proper base change for
`Rf_!` on `D⁺_tors` ([Stacks, Tag 0F7L]). -/
theorem isZero_homology_derivedLowerShriek_of_geometricFibres
    (K : DerivedCategory.Plus (EtaleModules.{u, 0} Λ X)) (m : ℕ) (hm : 0 < m) (hK : m • 𝟙 K = 0)
    (q : ℤ)
    (h : ∀ y : Y, IsZero ((DerivedCategory.Plus.homologyFunctor _ q).obj
      ((derivedLowerShriek.{u, 0} (pullback.snd f (GeometricPoint.ofPoint Y y).hom)
        (j.baseChange (IsPullback.of_hasPullback f (GeometricPoint.ofPoint Y y).hom)) Λ).obj
        ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ
          (pullback.fst f (GeometricPoint.ofPoint Y y).hom)).obj K)))) :
    IsZero ((DerivedCategory.Plus.homologyFunctor _ q).obj
      ((derivedLowerShriek.{u, 0} f j Λ).obj K)) := by
  refine isZero_of_forall_isZero_etaleModuleInverseImage Λ
    (fun y : Y => (GeometricPoint.ofPoint Y y).hom) (iUnion_range_geometricPoint_ofPoint Y) _
    fun y => ?_
  let s := (GeometricPoint.ofPoint Y y).hom
  let sq := IsPullback.of_hasPullback f s
  have := isIso_derivedLowerShriekBaseChange_app Λ sq j K
    (isTorsionPlus_of_nsmul_id_eq_zero K m hm hK)
  obtain ⟨e⟩ := nonempty_homology_etaleModuleDerivedInverseImagePlus_iso Λ s
    ((derivedLowerShriek.{u, 0} f j Λ).obj K) q
  exact (h y).of_iso ((DerivedCategory.Plus.homologyFunctor _ q).mapIso
    (asIso ((derivedLowerShriekBaseChange.{u, 0} Λ sq j).app K)).symm ≪≫ e).symm

end Stacks.EtaleCohomology

end
