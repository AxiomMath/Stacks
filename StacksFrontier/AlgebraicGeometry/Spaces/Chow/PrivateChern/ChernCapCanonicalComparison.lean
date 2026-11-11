module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ChernClassBivariantComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ChernClassChowCohomologyAlgebra

/-!
# The Chern classes of `A^*(X)` acting on Chow homology

In Situation 0EDT let `X/B` be good and let `ℰ` be a finite locally free `𝒪_X`-module of rank
`r`. On a good test space `g : X' ⟶ X` the maps `c_j(ℰ) ∩ - : CH_k(X') ⟶ CH_{k-j}(X')` of
Stacks 0ERY (`AlgebraicGeometry.Space.chernCap`) are the operations
`AlgebraicGeometry.Space.PrivateChern.chernCap` of `g^*ℰ` on `CH_*(X') = ⨁_k CH_k(X')`
(`AlgebraicGeometry.Space.chowGroupCanonicalToChowHomology_chernCap`). This file assembles them
into endomorphisms of `CH_*(X')` and reads off the action of the Chern classes of the Chow
cohomology ring `A^*(X)` (`AlgebraicGeometry.Space.ChowCohomologyAlgebra`) on `CH_*(X')`.

## Main definitions

* `AlgebraicGeometry.Space.chernCapChowHomology`: `c_j(ℰ) ∩ -` on `CH_*(X')`, homogeneous of
  degree `-j`.

## Main results

* `AlgebraicGeometry.Space.chernCapChowHomology_eq_chernCap`: it is
  `AlgebraicGeometry.Space.PrivateChern.chernCap` of `g^*ℰ`.
* `AlgebraicGeometry.Space.ChowCohomologyAlgebra.capChowHomology_totalChernClass_eq_totalChernCap`:
  the total Chern class `c(ℰ) ∈ A^*(X)` acts on `CH_*(X')` as the total Chern class of `g^*ℰ`.

## References

* [Stacks Project, Tag 0ERY](https://stacks.math.columbia.edu/tag/0ERY)
* [Stacks Project, Tag 0ERZ](https://stacks.math.columbia.edu/tag/0ERZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

open PrivateChern

section Comparison

variable {D : BaseSpaceDimensionSituation.{u}}

/-- Homomorphisms out of `CH_*(X)` are determined on the images of the Chow groups of
Stacks 0EQ6. -/
theorem chowHomology_hom_ext_chowGroupCanonical {X : D.Ambient} {sX : X ⟶ D.space}
    {hX : D.IsGood sX} {M : Type*} [AddCommMonoid M] {φ ψ : chowHomology.{u, u + 1} D sX hX →+ M}
    (h : ∀ (k : ℤ) (α : chowGroupCanonical.{u + 1} D sX hX k),
      φ (chowGroupCanonicalToChowHomology D sX hX k α) =
        ψ (chowGroupCanonicalToChowHomology D sX hX k α)) : φ = ψ :=
  chowHomology_hom_ext D sX hX fun k b => h k (chowClassCanonical.{u + 1} D sX hX k b)

/-- Endomorphisms of `CH_*(X)` are determined on the images of the Chow groups of Stacks 0EQ6. -/
theorem chowHomology_end_ext {X : D.Ambient} {sX : X ⟶ D.space} {hX : D.IsGood sX}
    {φ ψ : AddMonoid.End (chowHomology.{u, u + 1} D sX hX)}
    (h : ∀ (k : ℤ) (α : chowGroupCanonical.{u + 1} D sX hX k),
      φ (chowGroupCanonicalToChowHomology D sX hX k α) =
        ψ (chowGroupCanonicalToChowHomology D sX hX k α)) : φ = ψ := by
  exact chowHomology_hom_ext_chowGroupCanonical h

end Comparison

section Chern

variable {D : BaseSpaceDimensionSituation.{u}} {X : D.Ambient} {sX : X ⟶ D.space}
    {hX : D.IsGood sX} {E : Modules.{u, u} D.site D.base D.base_mem X hX.1} {r : ℕ}
    {hE : RingedSite.IsFiniteLocallyFreeOfRank
      (smallEtaleRingedSite D.site D.base D.base_mem X hX.1) E r}

variable (D sX hX E r hE) in
include hE in
/-- The inverse image `g^*ℰ` of a module of rank `r` to a good test space `g : X' ⟶ X` has rank
`r`. -/
theorem isFiniteLocallyFreeOfRank_spaceModulePullback_obj {Y : D.Ambient} (g : Y ⟶ X)
    (hY : D.IsGood (g ≫ sX)) :
    PrivateChern.IsFiniteLocallyFreeOfRank D (g ≫ sX) hY
      ((spaceModulePullback D hX.1 hY.1 g).obj E) r :=
  isFiniteLocallyFreeOfRank_modulePullback D.site D.base D.base_mem
    (ObjectProperty.homMk g : (⟨Y, hY.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨X, hX.1⟩) E
    r hE

/-- The summand inclusions of `CH_*(X)` do not see the identification `chowGroupDegreeCongr` of
Chow groups in equal degrees. -/
theorem of_chowGroupDegreeCongr {X : D.Ambient} (sX : X ⟶ D.space) (hX : D.IsGood sX) {a b : ℤ}
    (h : a = b) (y : chowGroup.{u + 1} D sX hX a) :
    DirectSum.of (fun k => chowGroup.{u + 1} D sX hX k) b
        (chowGroupDegreeCongr.{u, u + 1} D sX hX h y) =
      DirectSum.of (fun k => chowGroup.{u + 1} D sX hX k) a y := by
  subst h
  rfl

variable (D sX hX E r hE) in
/-- **The operation `c_j(ℰ) ∩ -` of Stacks 0ERY on the Chow homology of a test space**
`g : X' ⟶ X`: `AlgebraicGeometry.Space.chernCap` on each `CH_k(X')`, homogeneous of degree
`-j` on `CH_*(X') = ⨁_k CH_k(X')`. -/
def chernCapChowHomology {Y : D.Ambient} (g : Y ⟶ X) (hY : D.IsGood (g ≫ sX)) (j : Fin (r + 1)) :
    AddMonoid.End (chowHomology.{u, u + 1} D (g ≫ sX) hY) :=
  gradedChowMap.{u, u + 1} D (g ≫ sX) hY (g ≫ sX) hY (-((j : ℕ) : ℤ)) fun k =>
    (chowGroupDegreeCongr.{u, u + 1} D (g ≫ sX) hY (sub_eq_add_neg k _)).toAddMonoidHom.comp
      ((chowGroupCanonicalEquivChowGroup.{u + 1} D (g ≫ sX) hY
          (k - ((j : ℕ) : ℤ))).toAddMonoidHom.comp
        ((chernCap D sX hX E r hE g hY j k).comp
          (chowGroupCanonicalEquivChowGroup.{u + 1} D (g ≫ sX) hY k).symm.toAddMonoidHom))

/-- `chernCapChowHomology` on the summand `CH_k(X')` is `AlgebraicGeometry.Space.chernCap`. -/
theorem chernCapChowHomology_chowGroupCanonicalToChowHomology {Y : D.Ambient} (g : Y ⟶ X)
    (hY : D.IsGood (g ≫ sX)) (j : Fin (r + 1)) (k : ℤ)
    (α : chowGroupCanonical.{u + 1} D (g ≫ sX) hY k) :
    chernCapChowHomology D sX hX E r hE g hY j
        (chowGroupCanonicalToChowHomology D (g ≫ sX) hY k α) =
      chowGroupCanonicalToChowHomology D (g ≫ sX) hY (k - ((j : ℕ) : ℤ))
        (chernCap D sX hX E r hE g hY j k α) := by
  change (gradedChowMap.{u, u + 1} D (g ≫ sX) hY (g ≫ sX) hY (-((j : ℕ) : ℤ)) _ :
      chowHomology.{u, u + 1} D (g ≫ sX) hY →+ chowHomology.{u, u + 1} D (g ≫ sX) hY)
    (DirectSum.of (fun k => chowGroup.{u + 1} D (g ≫ sX) hY k) k
      (chowGroupCanonicalEquivChowGroup.{u + 1} D (g ≫ sX) hY k α)) = _
  rw [gradedChowMap_of]
  simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, AddEquiv.symm_apply_apply]
  exact of_chowGroupDegreeCongr _ _ _ _

/-- **The operation `c_j(ℰ) ∩ -` on Chow homology is that of `g^*ℰ`**:
`AlgebraicGeometry.Space.chowGroupCanonicalToChowHomology_chernCap` as an identity of
endomorphisms of `CH_*(X')`. -/
theorem chernCapChowHomology_eq_chernCap {Y : D.Ambient} (g : Y ⟶ X)
    (hY : D.IsGood (g ≫ sX)) (j : Fin (r + 1)) :
    chernCapChowHomology D sX hX E r hE g hY j =
      PrivateChern.chernCap.{u, u + 1} ((spaceModulePullback D hX.1 hY.1 g).obj E) r
        (isFiniteLocallyFreeOfRank_spaceModulePullback_obj D sX hX E r hE g hY) j :=
  chowHomology_end_ext fun k α => by
    rw [chernCapChowHomology_chowGroupCanonicalToChowHomology,
      chowGroupCanonicalToChowHomology_chernCap]

/-- **The Chern class `c_j(ℰ) ∈ A^j(X)` acts on the Chow homology of a test space
`g : X' ⟶ X` as `c_j(g^*ℰ)`**: the cap operation of
`AlgebraicGeometry.Space.ChowCohomologyClass.chernClass` on `CH_*(X')` is the operation
`AlgebraicGeometry.Space.PrivateChern.chernCap` of `g^*ℰ`. -/
theorem ChowCohomologyClass.capChowHomology_chernClass {Y : D.Ambient} (g : Y ⟶ X)
    (hY : D.IsGood (g ≫ sX)) (j : Fin (r + 1)) :
    ((ChowCohomologyClass.chernClass D sX hX E r hE j).capChowHomology g hY :
        AddMonoid.End (chowHomology.{u, u + 1} D (g ≫ sX) hY)) =
      PrivateChern.chernCap.{u, u + 1} ((spaceModulePullback D hX.1 hY.1 g).obj E) r
        (isFiniteLocallyFreeOfRank_spaceModulePullback_obj D sX hX E r hE g hY) j := by
  rw [← chernCapChowHomology_eq_chernCap (hX := hX) (hE := hE)]
  refine chowHomology_end_ext fun k α => ?_
  rw [chernCapChowHomology_chowGroupCanonicalToChowHomology]
  exact ChowCohomologyClass.chernClass_capChowHomology_of D sX hX E r hE j g hY k α

/-- **The total Chern class `c(ℰ) ∈ A^*(X)` acts on the Chow homology of a test space
`g : X' ⟶ X` as the total Chern class of `g^*ℰ`**
(`AlgebraicGeometry.Space.PrivateChern.totalChernCap`). -/
theorem ChowCohomologyAlgebra.capChowHomology_totalChernClass_eq_totalChernCap {Y : D.Ambient}
    (g : Y ⟶ X) (hY : D.IsGood (g ≫ sX)) :
    ChowCohomologyAlgebra.capChowHomology g hY
        (ChowCohomologyAlgebra.totalChernClass D sX hX E r hE) =
      PrivateChern.totalChernCap.{u, u + 1} ((spaceModulePullback D hX.1 hY.1 g).obj E) r
        (isFiniteLocallyFreeOfRank_spaceModulePullback_obj D sX hX E r hE g hY) := by
  rw [ChowCohomologyAlgebra.capChowHomology_totalChernClass, PrivateChern.totalChernCap,
    ← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl fun j _ => ChowCohomologyClass.capChowHomology_chernClass g hY j

end Chern

end AlgebraicGeometry.Space

end
