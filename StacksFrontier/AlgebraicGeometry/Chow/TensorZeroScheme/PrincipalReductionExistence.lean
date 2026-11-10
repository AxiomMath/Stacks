module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.ZeroSectionBranchChowIdentity
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Canonical
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.BaseChangeIsoGysinSystem
public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.PrincipalReduction

/-!
# The existence of the reduction of a Cartier Gysin map to a principal divisor

[Stacks, Tag 0F99] asserts that for a scheme `X` locally of finite type over the base situation of
chapter 42 and a triple `(ℒ, s, i : D ⟶ X)` as in [Stacks, Tag 02T8] there is a commutative square

  `D' --i'--> X'`
  `|p         |g`
  `D --i-->   X`

with the four properties collected in
`Stacks.Chow.TensorZeroScheme.PrincipalReduction`. This file constructs one.

The source's proof: set `ℒ₁ = 𝒪_X` and `ℒ₂ = ℒ` and apply [Stacks, Tag 0F97] to `s`, read as a
section of `ℒ₁ ⊗ ℒ₂`; take `D' = D₁`. Then `g` is the projection `p : L ⟶ X` of that tag's
diagram and `p` is its `p₁ : D₁ ⟶ D`; clause (1) is clause (2) of [Stacks, Tag 0F97] for `g`
and the line-bundle presentation of `D₁` for `p`, clause (2) is [Stacks, Tag 0B74], clause (3)
holds because `s₁` is a section of `p^*𝒪_X ≅ 𝒪_L`, and clause (4) is [Stacks, Tag 0F98].

## Main definitions

* `Stacks.Chow.TensorZeroScheme.presentationMap`: the morphism `Z(t) ⟶ Z(s)` of a square whose
  two divisors are presented as ideal sheaves equal to `Z(t)` and `Z(s)`; the two changes of
  presentation of the source's proof are absorbed here.
* `Stacks.Chow.TensorZeroScheme.principalReductionOfDecomposition`: the reduction attached to an
  arbitrary diagram of [Stacks, Tag 0F97] whose first module is trivialized.
* `Stacks.Chow.TensorZeroScheme.principalReductionBaseChange`: the reduction attached to the
  base change of such a diagram along an arbitrary cartesian square.
* `Stacks.Chow.TensorZeroScheme.principalReduction`: the reduction of the given divisor.

## Main results

* `Stacks.Chow.heq_gysinChowOfInvertible_of_moduleIso`: the Gysin map of [Stacks, Tag 02TO]
  depends on the pair `(L, s)` only through its isomorphism class.
* `Stacks.Chow.TensorZeroScheme.principalReductionOfDecomposition_isStableUnderBaseChange`: the
  closing base-change assertion of [Stacks, Tag 0F99] for these reductions.
* `Stacks.Chow.TensorZeroScheme.exists_principalReduction_isStableUnderBaseChange`:
  **[Stacks, Tag 0F99]**.

## Implementation notes

### The two changes of presentation

The source writes `ℒ = 𝒪_X ⊗ ℒ` and `D₁ = Z(s₁) = Z(s')` without comment. Formally these are two
equalities of ideal sheaves between terms neither of which is the other: the divisor of the
diagram is the zero scheme of `s` read in `𝒪_X ⊗ ℒ`, and its first branch is the zero scheme of
the section `s₁` of `p^*𝒪_X` rather than of a global function. `presentationMap` reads the branch
projection through the inclusions of equal ideal sheaves, so the upper corner, the map `g` and the
global function of clause (3) are the diagram's own data, by definition; the equalities enter only
in the proofs of clauses (2) and (4), where they are eliminated by `subst`.

### Why the reduction is built from an arbitrary diagram

The base change of the constructed diagram of [Stacks, Tag 0F97] is a diagram as in that tag
(`Stacks.Chow.TensorZeroScheme.Decomposition.baseChange`), but it is not known to be the
constructed diagram of the base-changed data. So clause (4) of the base-changed square cannot be
read off [Stacks, Tag 0F98] for the construction; it is [Stacks, Tag 0F98] for the base-changed
diagram, which is why that tag is proved for every diagram. The upper corner of the base-changed
square is the given cartesian square's corner, by definition, which is what lets
[Stacks, Tag 0F9A] take it to be the base change used by the cap operation of a bivariant class.

## References

* [Stacks Project, Tag 0F99](https://stacks.math.columbia.edu/tag/0F99)
* [Stacks Project, Tag 0F97](https://stacks.math.columbia.edu/tag/0F97)
* [Stacks Project, Tag 0F98](https://stacks.math.columbia.edu/tag/0F98)
* [Stacks Project, Tag 0B74](https://stacks.math.columbia.edu/tag/0B74)
* [Stacks Project, Tag 02OQ](https://stacks.math.columbia.edu/tag/02OQ)
* [Stacks Project, Tag 02T8](https://stacks.math.columbia.edu/tag/02T8)
* [Stacks Project, Tag 02TO](https://stacks.math.columbia.edu/tag/02TO)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open Stacks.PullbackTensorIso (pullbackTensorSection)

universe u

namespace Stacks.Chow

/-- **The Gysin map of [Stacks, Tag 02TO] depends on the pair `(L, s)` only through its
isomorphism class.** If `L ≅ M` and the zero schemes of `s` and `t` agree, the two Gysin maps are
heterogeneously equal.

This is `Stacks.Chow.gysinSystemOfInvertible_onChow_heq_of_moduleIso` read at the canonical Gysin
system, whose Gysin map on Chow groups is `Stacks.Chow.gysinChowOfInvertible` by
`Stacks.Chow.canonicalGysinSystem_onChow`. -/
theorem heq_gysinChowOfInvertible_of_moduleIso (C : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ) {M N : X.Modules}
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M]
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
    (sM : Γ(M, ⊤)) (sN : Γ(N, ⊤)) (φ : M ≅ N)
    (hz : Stacks.Divisors.zeroScheme X M sM = Stacks.Divisors.zeroScheme X N sN) :
    HEq (gysinChowOfInvertible C p k M sM) (gysinChowOfInvertible C p k N sN) :=
  gysinSystemOfInvertible_onChow_heq_of_moduleIso C (gysinOfInvertibleDescends C) p k sM sN φ hz

namespace TensorZeroScheme

/-- Flat pullback on Chow groups along two equal morphisms is the same map. -/
theorem flatPullbackChowOfRelativeDimension_congr_hom (C : ChowSituation.{u}) {X' X : Scheme.{u}}
    (sX' : X' ⟶ C.S) [LocallyOfFiniteType sX'] (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    {f f' : X' ⟶ X} [LocallyOfFiniteType f] [Flat f] [LocallyOfFiniteType f'] [Flat f']
    (h : f = f') (hb : f ≫ sX = sX') (hb' : f' ≫ sX = sX') (r : ℕ)
    (hr : AlgebraicGeometry.RelativeDimension f r)
    (hr' : AlgebraicGeometry.RelativeDimension f' r) (k : ℤ) :
    flatPullbackChowOfRelativeDimension C sX' sX f hb r hr k =
      flatPullbackChowOfRelativeDimension C sX' sX f' hb' r hr' k := by
  subst h
  rfl

section Presentation

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (L : X.Modules)
  [hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  (s : Γ(L, ⊤)) {X' : Scheme.{u}} (g : X' ⟶ X) [LocallyOfFiniteType g]
  (t : Γ(Scheme.unitModule X', ⊤))

include hL in
/-- The morphism `Z(t) ⟶ Z(s)` of a square whose two divisors are presented as ideal sheaves
`B` and `D₀` equal to `Z(t)` and `Z(s)`: the given `q : B ⟶ D₀` read through the inclusions of
equal ideal sheaves. -/
def presentationMap {D₀ : X.IdealSheafData} (hD₀ : Stacks.Divisors.zeroScheme X L s = D₀)
    {B : X'.IdealSheafData} (hB : Stacks.Divisors.zeroScheme X' (Scheme.unitModule X') t = B)
    (q : B.subscheme ⟶ D₀.subscheme) :
    (Stacks.Divisors.zeroScheme X' (Scheme.unitModule X') t).subscheme ⟶
      (Stacks.Divisors.zeroScheme X L s).subscheme :=
  Scheme.IdealSheafData.inclusion hB.ge ≫ q ≫ Scheme.IdealSheafData.inclusion hD₀.le

omit [LocallyOfFiniteType g] in
include hL in
/-- `presentationMap` lies over the given square. -/
theorem presentationMap_comm {D₀ : X.IdealSheafData}
    (hD₀ : Stacks.Divisors.zeroScheme X L s = D₀) {B : X'.IdealSheafData}
    (hB : Stacks.Divisors.zeroScheme X' (Scheme.unitModule X') t = B)
    (q : B.subscheme ⟶ D₀.subscheme) (hcomm : B.subschemeι ≫ g = q ≫ D₀.subschemeι) :
    (Stacks.Divisors.zeroScheme X' (Scheme.unitModule X') t).subschemeι ≫ g =
      presentationMap L s t hD₀ hB q ≫ (Stacks.Divisors.zeroScheme X L s).subschemeι := by
  rw [presentationMap, Category.assoc, Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι,
    ← hcomm, ← Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι]

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType g] in
include hL in
/-- The structure morphisms of the two divisors of `presentationMap` agree. -/
theorem presentationMap_base {D₀ : X.IdealSheafData}
    (hD₀ : Stacks.Divisors.zeroScheme X L s = D₀) {B : X'.IdealSheafData}
    (hB : Stacks.Divisors.zeroScheme X' (Scheme.unitModule X') t = B)
    (q : B.subscheme ⟶ D₀.subscheme) (hcomm : B.subschemeι ≫ g = q ≫ D₀.subschemeι) :
    presentationMap L s t hD₀ hB q ≫ (Stacks.Divisors.zeroScheme X L s).subschemeι ≫ sX =
      (Stacks.Divisors.zeroScheme X' (Scheme.unitModule X') t).subschemeι ≫ g ≫ sX := by
  rw [← Category.assoc, ← presentationMap_comm L s g t hD₀ hB q hcomm, Category.assoc]

/-- `presentationMap` for the identity presentations is the given morphism. -/
private theorem presentationMap_rfl
    (q : (Stacks.Divisors.zeroScheme X' (Scheme.unitModule X') t).subscheme ⟶
      (Stacks.Divisors.zeroScheme X L s).subscheme) :
    presentationMap L s t rfl rfl q = q := by
  simp only [presentationMap, Scheme.IdealSheafData.inclusion_id, Category.id_comp,
    Category.comp_id]

include hL in
/-- `presentationMap` is locally of finite type when `q` is. -/
theorem locallyOfFiniteType_presentationMap {D₀ : X.IdealSheafData}
    (hD₀ : Stacks.Divisors.zeroScheme X L s = D₀) {B : X'.IdealSheafData}
    (hB : Stacks.Divisors.zeroScheme X' (Scheme.unitModule X') t = B)
    (q : B.subscheme ⟶ D₀.subscheme) (hq : LocallyOfFiniteType q) :
    LocallyOfFiniteType (presentationMap L s t hD₀ hB q) := by
  subst hD₀ hB
  rw [presentationMap_rfl]
  exact hq

include hL in
/-- `presentationMap` is quasi-compact when `q` is. -/
theorem quasiCompact_presentationMap {D₀ : X.IdealSheafData}
    (hD₀ : Stacks.Divisors.zeroScheme X L s = D₀) {B : X'.IdealSheafData}
    (hB : Stacks.Divisors.zeroScheme X' (Scheme.unitModule X') t = B)
    (q : B.subscheme ⟶ D₀.subscheme) (hq : QuasiCompact q) :
    QuasiCompact (presentationMap L s t hD₀ hB q) := by
  subst hD₀ hB
  rw [presentationMap_rfl]
  exact hq

include hL in
/-- `presentationMap` is flat when `q` is. -/
theorem flat_presentationMap {D₀ : X.IdealSheafData}
    (hD₀ : Stacks.Divisors.zeroScheme X L s = D₀) {B : X'.IdealSheafData}
    (hB : Stacks.Divisors.zeroScheme X' (Scheme.unitModule X') t = B)
    (q : B.subscheme ⟶ D₀.subscheme) (hq : AlgebraicGeometry.Flat q) :
    AlgebraicGeometry.Flat (presentationMap L s t hD₀ hB q) := by
  subst hD₀ hB
  rw [presentationMap_rfl]
  exact hq

include hL in
/-- `presentationMap` has relative dimension `1` when `q` does. -/
theorem relativeDimension_presentationMap {D₀ : X.IdealSheafData}
    (hD₀ : Stacks.Divisors.zeroScheme X L s = D₀) {B : X'.IdealSheafData}
    (hB : Stacks.Divisors.zeroScheme X' (Scheme.unitModule X') t = B)
    (q : B.subscheme ⟶ D₀.subscheme) (hqft : LocallyOfFiniteType q)
    (hqdim : letI : LocallyOfFiniteType q := hqft; AlgebraicGeometry.RelativeDimension q 1) :
    letI : LocallyOfFiniteType (presentationMap L s t hD₀ hB q) :=
      locallyOfFiniteType_presentationMap L s t hD₀ hB q hqft
    AlgebraicGeometry.RelativeDimension (presentationMap L s t hD₀ hB q) 1 := by
  subst hD₀ hB
  simp only [presentationMap_rfl]
  exact hqdim

include hL in
/-- Clauses (2) and (4) of [Stacks, Tag 0F99] for `presentationMap`, from the same clauses for
`q` and the identification of each of the Gysin maps involved with the canonical one. -/
theorem presentationMap_clauses {D₀ : X.IdealSheafData}
    (hD₀ : Stacks.Divisors.zeroScheme X L s = D₀) {B : X'.IdealSheafData}
    (hB : Stacks.Divisors.zeroScheme X' (Scheme.unitModule X') t = B)
    (q : B.subscheme ⟶ D₀.subscheme) [AlgebraicGeometry.Flat g]
    (hgdim : AlgebraicGeometry.RelativeDimension g 1)
    [hq₁ : LocallyOfFiniteType q] [hq₂ : AlgebraicGeometry.Flat q]
    (hqdim : AlgebraicGeometry.RelativeDimension q 1)
    (hbase : q ≫ D₀.subschemeι ≫ sX = B.subschemeι ≫ g ≫ sX)
    (hinj : ∀ k : ℤ, Function.Injective (flatPullbackChowOfRelativeDimension C
      (B.subschemeι ≫ g ≫ sX) (D₀.subschemeι ≫ sX) q hbase 1 hqdim k))
    (γ : ∀ k : ℤ, chowGroup C sX (k + 1) →+ chowGroup C (D₀.subschemeι ≫ sX) k)
    (hγ : ∀ k : ℤ, HEq (γ k) (gysinChowOfInvertible C sX k L s))
    (gBr : ∀ k : ℤ,
      chowGroup C (g ≫ sX) (k + 1) →+ chowGroup C (B.subschemeι ≫ g ≫ sX) k)
    (hgBr : ∀ k : ℤ,
      HEq (gBr k) (gysinChowOfInvertible C (g ≫ sX) k (Scheme.unitModule X') t))
    (hgysin : ∀ (k : ℤ) (α : chowGroup C sX (k + 1)),
      gBr (k + 1) (flatPullbackChowOfRelativeDimension C (g ≫ sX) sX g rfl 1 hgdim (k + 1) α) =
        flatPullbackChowOfRelativeDimension C (B.subschemeι ≫ g ≫ sX) (D₀.subschemeι ≫ sX) q
          hbase 1 hqdim k (γ k α))
    [hp₁ : LocallyOfFiniteType (presentationMap L s t hD₀ hB q)]
    [hp₂ : AlgebraicGeometry.Flat (presentationMap L s t hD₀ hB q)]
    (hpdim : AlgebraicGeometry.RelativeDimension (presentationMap L s t hD₀ hB q) 1)
    (hpbase : presentationMap L s t hD₀ hB q ≫ (Stacks.Divisors.zeroScheme X L s).subschemeι ≫ sX =
      (Stacks.Divisors.zeroScheme X' (Scheme.unitModule X') t).subschemeι ≫ g ≫ sX) :
    (∀ k : ℤ, Function.Injective (flatPullbackChowOfRelativeDimension C
      ((Stacks.Divisors.zeroScheme X' (Scheme.unitModule X') t).subschemeι ≫ g ≫ sX)
      ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ sX) (presentationMap L s t hD₀ hB q)
      hpbase 1 hpdim k)) ∧
    ∀ (k : ℤ) (α : chowGroup C sX (k + 1)),
      gysinChowOfInvertible C (g ≫ sX) (k + 1) (Scheme.unitModule X') t
          (flatPullbackChowOfRelativeDimension C (g ≫ sX) sX g rfl 1 hgdim (k + 1) α) =
        flatPullbackChowOfRelativeDimension C
          ((Stacks.Divisors.zeroScheme X' (Scheme.unitModule X') t).subschemeι ≫ g ≫ sX)
          ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ sX)
          (presentationMap L s t hD₀ hB q) hpbase 1 hpdim k
          (gysinChowOfInvertible C sX k L s α) := by
  subst hD₀ hB
  have hp := presentationMap_rfl L s t q
  refine ⟨fun k => ?_, fun k α => ?_⟩
  · rw [flatPullbackChowOfRelativeDimension_congr_hom C _ _ hp hpbase hbase 1 hpdim hqdim k]
    exact hinj k
  · rw [flatPullbackChowOfRelativeDimension_congr_hom C _ _ hp hpbase hbase 1 hpdim hqdim k,
      ← eq_of_heq (hgBr (k + 1)), hgysin k α, eq_of_heq (hγ k)]

end Presentation

/-! ### The reduction attached to a diagram of Tag 0F97 -/

section OfDecomposition

variable {X : Scheme.{u}} {L₁ L₂ : X.Modules}
  [h₁ : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L₁]
  [h₂ : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L₂]
  {t : Γ(Stacks.Divisors.tensorModules L₁ L₂, ⊤)} (R : Decomposition X L₁ L₂ t)
  (ε : L₁ ≅ Scheme.unitModule X)

include h₁ h₂ in
/-- **The global function cutting out the first branch** of a diagram as in [Stacks, Tag 0F97]
whose first module is trivialized: the section `s₁` of `p^*L₁` read through `p^*L₁ ≅ 𝒪`. -/
def Decomposition.unitEquation : Γ(Scheme.unitModule R.total, ⊤) :=
  Scheme.Modules.Hom.app (pullbackIsoUnitModule R.p ε).hom ⊤ R.s₁

include h₁ h₂ in
/-- **Clause (3) of [Stacks, Tag 0F99] for a diagram of [Stacks, Tag 0F97] with trivialized first
module**: its first branch is the zero scheme of the global function
`Stacks.Chow.TensorZeroScheme.Decomposition.unitEquation`. -/
theorem Decomposition.zeroScheme_unitEquation :
    Stacks.Divisors.zeroScheme R.total (Scheme.unitModule R.total) (R.unitEquation ε) =
      R.normalize.D₁ :=
  (AlgebraicGeometry.zeroScheme_eq_of_iso (pullbackIsoUnitModule R.p ε) rfl).symm

variable (C : ChowSituation.{u}) (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (L : X.Modules)
  [hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  (s : Γ(L, ⊤)) (φ : Stacks.Divisors.tensorModules L₁ L₂ ≅ L)
  (hz : zeroIdeal X L₁ L₂ t = Stacks.Divisors.zeroScheme X L s)

include h₁ h₂ hL φ in
/-- Clauses (2) and (4) of [Stacks, Tag 0F99] for the square attached to a diagram of
[Stacks, Tag 0F97]: [Stacks, Tag 0B74] and [Stacks, Tag 0F98] for the diagram, read through the
two changes of presentation. -/
theorem Decomposition.presentationMap_clauses_of_decomposition :
    letI : LocallyOfFiniteType (presentationMap L s (R.unitEquation ε) hz.symm
        (R.zeroScheme_unitEquation ε) R.normalize.p₁) :=
      locallyOfFiniteType_presentationMap L s _ _ _ _
        (Decomposition.locallyOfFiniteType_p₁ X L₁ L₂ t R.normalize)
    letI : AlgebraicGeometry.Flat (presentationMap L s (R.unitEquation ε) hz.symm
        (R.zeroScheme_unitEquation ε) R.normalize.p₁) :=
      flat_presentationMap L s _ _ _ _ (Decomposition.flat_p₁ X L₁ L₂ t R.normalize)
    (∀ k : ℤ, Function.Injective (flatPullbackChowOfRelativeDimension C
      ((Stacks.Divisors.zeroScheme R.total (Scheme.unitModule R.total)
        (R.unitEquation ε)).subschemeι ≫ R.p ≫ sX)
      ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ sX)
      (presentationMap L s (R.unitEquation ε) hz.symm (R.zeroScheme_unitEquation ε)
        R.normalize.p₁)
      (presentationMap_base C sX L s R.p (R.unitEquation ε) hz.symm
        (R.zeroScheme_unitEquation ε) R.normalize.p₁ R.normalize.comm₁) 1
      (relativeDimension_presentationMap L s (R.unitEquation ε) hz.symm
        (R.zeroScheme_unitEquation ε) R.normalize.p₁
        (Decomposition.locallyOfFiniteType_p₁ X L₁ L₂ t R.normalize)
        (Decomposition.relativeDimension_p₁ X L₁ L₂ t R.normalize)) k)) ∧
    ∀ (k : ℤ) (α : chowGroup C sX (k + 1)),
      gysinChowOfInvertible C (R.p ≫ sX) (k + 1) (Scheme.unitModule R.total) (R.unitEquation ε)
          (flatPullbackChowOfRelativeDimension C (R.p ≫ sX) sX R.p rfl 1 R.p_relativeDimension
            (k + 1) α) =
        flatPullbackChowOfRelativeDimension C
          ((Stacks.Divisors.zeroScheme R.total (Scheme.unitModule R.total)
            (R.unitEquation ε)).subschemeι ≫ R.p ≫ sX)
          ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ sX)
          (presentationMap L s (R.unitEquation ε) hz.symm (R.zeroScheme_unitEquation ε)
            R.normalize.p₁)
          (presentationMap_base C sX L s R.p (R.unitEquation ε) hz.symm
            (R.zeroScheme_unitEquation ε) R.normalize.p₁ R.normalize.comm₁) 1
          (relativeDimension_presentationMap L s (R.unitEquation ε) hz.symm
            (R.zeroScheme_unitEquation ε) R.normalize.p₁
            (Decomposition.locallyOfFiniteType_p₁ X L₁ L₂ t R.normalize)
            (Decomposition.relativeDimension_p₁ X L₁ L₂ t R.normalize)) k
          (gysinChowOfInvertible C sX k L s α) :=
  presentationMap_clauses C sX L s R.p (R.unitEquation ε) hz.symm
    (R.zeroScheme_unitEquation ε) R.normalize.p₁ R.p_relativeDimension
    (hq₁ := Decomposition.locallyOfFiniteType_p₁ X L₁ L₂ t R.normalize)
    (hq₂ := Decomposition.flat_p₁ X L₁ L₂ t R.normalize)
    (Decomposition.relativeDimension_p₁ X L₁ L₂ t R.normalize)
    (proj₁_comp_zeroIdeal_subschemeι_comp C X L₁ L₂ t R sX)
    (fun k => flatPullbackChowProj₁_injective C X L₁ L₂ t R sX k)
    (fun k => gysinChowZeroIdeal C X L₁ L₂ t sX k)
    (fun k => heq_gysinChowOfInvertible_of_moduleIso C sX k t s φ hz)
    (fun k => gysinChowBranch₁ C X L₁ L₂ t R sX k)
    (fun k => heq_gysinChowOfInvertible_of_moduleIso C (R.p ≫ sX) k R.s₁ (R.unitEquation ε)
      (pullbackIsoUnitModule R.p ε) (R.zeroScheme_unitEquation ε).symm)
    (fun k α => gysinChowBranch₁_flatPullbackChowProj C X L₁ L₂ t R sX k α)
    (hp₁ := locallyOfFiniteType_presentationMap L s _ _ _ _
      (Decomposition.locallyOfFiniteType_p₁ X L₁ L₂ t R.normalize))
    (hp₂ := flat_presentationMap L s _ _ _ _ (Decomposition.flat_p₁ X L₁ L₂ t R.normalize))
    _ _

include h₁ h₂ hL φ in
/-- **The reduction of [Stacks, Tag 0F99] attached to a diagram of [Stacks, Tag 0F97].** For a
diagram `R` for a section `t` of `L₁ ⊗ L₂` with `L₁ ≅ 𝒪_X`, `L₁ ⊗ L₂ ≅ ℒ` and
`Z(t) = Z(s)`, the square is `D₁ ⟶ L` over `D ⟶ X`: the upper-right corner is the total space
`L` of the diagram and `g` its projection, `D'` is the first branch, cut out by the global
function `Stacks.Chow.TensorZeroScheme.Decomposition.unitEquation`, and `p` is the first branch
projection. Clause (1) is condition (2) of [Stacks, Tag 0F97] and the line-bundle presentation
of `D₁`, clause (2) is [Stacks, Tag 0B74], and clause (4) is [Stacks, Tag 0F98] for `R`. -/
def principalReductionOfDecomposition : PrincipalReduction C sX L s where
  X' := R.total
  g := R.p
  g_locallyOfFiniteType := R.p_locallyOfFiniteType
  g_quasiCompact := R.p_quasiCompact
  g_flat := R.p_flat
  g_relativeDimension := R.p_relativeDimension
  s' := R.unitEquation ε
  p := presentationMap L s (R.unitEquation ε) hz.symm (R.zeroScheme_unitEquation ε)
    R.normalize.p₁
  comm := presentationMap_comm L s R.p (R.unitEquation ε) hz.symm
    (R.zeroScheme_unitEquation ε) R.normalize.p₁ R.normalize.comm₁
  p_locallyOfFiniteType := locallyOfFiniteType_presentationMap L s _ _ _ _
    (Decomposition.locallyOfFiniteType_p₁ X L₁ L₂ t R.normalize)
  p_quasiCompact := quasiCompact_presentationMap L s _ _ _ _
    (quasiCompact_of_iso_totalSpace R.normalize.branch₁ R.normalize.branch₁_toBase)
  p_flat := flat_presentationMap L s _ _ _ _ (Decomposition.flat_p₁ X L₁ L₂ t R.normalize)
  p_relativeDimension := relativeDimension_presentationMap L s (R.unitEquation ε) hz.symm
    (R.zeroScheme_unitEquation ε) R.normalize.p₁
    (Decomposition.locallyOfFiniteType_p₁ X L₁ L₂ t R.normalize)
    (Decomposition.relativeDimension_p₁ X L₁ L₂ t R.normalize)
  flatPullbackBranch_injective := (R.presentationMap_clauses_of_decomposition ε C sX L s φ hz).1
  gysinBranch_flatPullbackAmbient :=
    (R.presentationMap_clauses_of_decomposition ε C sX L s φ hz).2

include h₁ h₂ hL φ in
/-- The first branch of `Stacks.Chow.TensorZeroScheme.principalReductionOfDecomposition` is the
first branch of the diagram. -/
theorem principalReductionOfDecomposition_branch :
    (principalReductionOfDecomposition R ε C sX L s φ hz).branch = R.normalize.D₁ :=
  R.zeroScheme_unitEquation ε

end OfDecomposition

/-! ### Base change -/

section BaseChange

variable {X : Scheme.{u}} {L₁ L₂ : X.Modules}
  [h₁ : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L₁]
  [h₂ : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L₂]
  {t : Γ(Stacks.Divisors.tensorModules L₁ L₂, ⊤)} (R : Decomposition X L₁ L₂ t)
  (ε : L₁ ≅ Scheme.unitModule X)
  (C : ChowSituation.{u}) (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (L : X.Modules)
  [hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  (s : Γ(L, ⊤)) (φ : Stacks.Divisors.tensorModules L₁ L₂ ≅ L)
  (hz : zeroIdeal X L₁ L₂ t = Stacks.Divisors.zeroScheme X L s)
  {Y : Scheme.{u}} (f : Y ⟶ X)

include h₁ h₂ hL φ in
/-- The data of the diagram base changed along `f`: `f^*L₁ ⊗ f^*L₂ ≅ f^*ℒ`, through the
comparison of [Stacks, Tag 01CD]. -/
def baseChangeModuleIso :
    Stacks.Divisors.tensorModules ((Scheme.Modules.pullback f).obj L₁)
        ((Scheme.Modules.pullback f).obj L₂) ≅ (Scheme.Modules.pullback f).obj L :=
  (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso f L₁ L₂).symm ≪≫
    (Scheme.Modules.pullback f).mapIso φ

include h₁ h₂ hL hz in
/-- The divisor of the diagram base changed along `f` is the zero scheme of `f^*s`
([Stacks, Tag 0B6Y]). -/
theorem zeroIdeal_baseChange_eq :
    zeroIdeal Y ((Scheme.Modules.pullback f).obj L₁) ((Scheme.Modules.pullback f).obj L₂)
        (pullbackTensorSection f L₁ L₂ t) =
      Stacks.Divisors.zeroScheme Y ((Scheme.Modules.pullback f).obj L)
        (AlgebraicGeometry.pullbackGlobalSections f L s) :=
  (comap_zeroIdeal t f).symm.trans ((congrArg (fun I : X.IdealSheafData => I.comap f) hz).trans
    (Stacks.Divisors.zeroScheme_pullback f L s).symm)

variable (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] {T' : Scheme.{u}} {k : T' ⟶ R.total}
  {p' : T' ⟶ Y} (hsq : IsPullback k p' R.p f)

include h₁ h₂ hL φ hz in
/-- **The reduction of [Stacks, Tag 0F99] base changed along `f : Y ⟶ X`**, for an arbitrary
cartesian square `T' = L ×_X Y`: the reduction attached to the base-changed diagram of
[Stacks, Tag 0F97] (`Stacks.Chow.TensorZeroScheme.Decomposition.baseChange`). Its upper-right
corner is `T'` and its map `g` is `p' : T' ⟶ Y`, both by definition. -/
def principalReductionBaseChange :
    letI : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property
      ((Scheme.Modules.pullback f).obj L) := Stacks.Divisors.pullback_isInvertible f L
    PrincipalReduction C sY ((Scheme.Modules.pullback f).obj L)
      (AlgebraicGeometry.pullbackGlobalSections f L s) :=
  letI : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property
      ((Scheme.Modules.pullback f).obj L₁) := Stacks.Divisors.pullback_isInvertible f L₁
  letI : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property
      ((Scheme.Modules.pullback f).obj L₂) := Stacks.Divisors.pullback_isInvertible f L₂
  letI : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property
      ((Scheme.Modules.pullback f).obj L) := Stacks.Divisors.pullback_isInvertible f L
  principalReductionOfDecomposition (R.normalize.baseChange f hsq) (pullbackIsoUnitModule f ε) C
    sY ((Scheme.Modules.pullback f).obj L) (AlgebraicGeometry.pullbackGlobalSections f L s)
    (baseChangeModuleIso L φ f) (zeroIdeal_baseChange_eq L s hz f)

include h₁ h₂ hL φ in
/-- **The first branch of the base-changed reduction is the inverse image of the first branch.**
-/
theorem principalReductionBaseChange_branch :
    (principalReductionBaseChange R ε C L s φ hz f sY hsq).branch =
      (principalReductionOfDecomposition R ε C sX L s φ hz).branch.comap k := by
  let : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property
      ((Scheme.Modules.pullback f).obj L₁) := Stacks.Divisors.pullback_isInvertible f L₁
  let : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property
      ((Scheme.Modules.pullback f).obj L₂) := Stacks.Divisors.pullback_isInvertible f L₂
  let : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property
      ((Scheme.Modules.pullback f).obj L) := Stacks.Divisors.pullback_isInvertible f L
  exact (principalReductionOfDecomposition_branch (R.normalize.baseChange f hsq)
    (pullbackIsoUnitModule f ε) C sY ((Scheme.Modules.pullback f).obj L)
    (AlgebraicGeometry.pullbackGlobalSections f L s) (baseChangeModuleIso L φ f)
    (zeroIdeal_baseChange_eq L s hz f)).trans
    ((R.normalize.comap_D₁_baseChange f hsq).symm.trans
      (congrArg (fun I : R.total.IdealSheafData => I.comap k)
        (principalReductionOfDecomposition_branch R ε C sX L s φ hz).symm))

include h₁ h₂ hL φ in
/-- **[Stacks, Tag 0F99], the closing assertion, for the reduction attached to a diagram of
[Stacks, Tag 0F97]**: its four properties remain true after base change by any morphism
`f : Y ⟶ X` locally of finite type. -/
theorem principalReductionOfDecomposition_isStableUnderBaseChange :
    (principalReductionOfDecomposition R ε C sX L s φ hz).IsStableUnderBaseChange := by
  intro Y f _
  exact ⟨principalReductionBaseChange R ε C L s φ hz f (f ≫ sX)
      (IsPullback.of_hasPullback R.p f),
    Limits.pullback.fst R.p f, IsPullback.of_hasPullback R.p f,
    principalReductionBaseChange_branch R ε C sX L s φ hz f (f ≫ sX)
      (IsPullback.of_hasPullback R.p f)⟩

end BaseChange

/-! ### The reduction of a divisor -/

section Reduction

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (L : X.Modules)
  [h : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  (s : Γ(L, ⊤))

include h in
/-- **[Stacks, Tag 0F99], the square and its four clauses, with nothing assumed.** For a scheme
`X` locally of finite type over the base situation of chapter 42 and a triple
`(ℒ, s, i : D ⟶ X)` as in [Stacks, Tag 02T8], the commutative square

  `D' --i'--> X'`
  `|p         |g`
  `D --i-->   X`

in which `g` and `p` are of finite type and flat of relative dimension one, `p^*` is injective on
`A_k(D)` for every `k`, `D'` is the zero scheme of a global section of `𝒪_{X'}`, and
`p^*i^* = (i')^*g^*`.

It is [Stacks, Tag 0F97] at `ℒ₁ = 𝒪_X`, `ℒ₂ = ℒ` with `D' = D₁`, read through
`Stacks.Chow.TensorZeroScheme.principalReductionOfDecomposition`. -/
def principalReduction : PrincipalReduction C sX L s :=
  principalReductionOfDecomposition (decomposition X (Scheme.unitModule X) L
      (unitTensorSection X L s)) (Iso.refl _) C sX L s (unitTensorUnitor X L)
    (zeroScheme_unitTensorSection X L s)

include h in
/-- **[Stacks, Tag 0F99].** For a scheme `X` locally of finite type over the base situation of
chapter 42 and a triple `(ℒ, s, i : D ⟶ X)` as in [Stacks, Tag 02T8] there is a commutative
square

  `D' --i'--> X'`
  `|p         |g`
  `D --i-->   X`

such that `p` and `g` are of finite type and flat of relative dimension `1`,
`p^* : A_k(D) ⟶ A_{k+1}(D')` is injective for all `k`, `D' ⊆ X'` is the zero scheme of a
global section of `𝒪_{X'}`, and `p^*i^* = (i')^*g^*`; and these properties remain true after
arbitrary base change by morphisms `Y ⟶ X` locally of finite type. -/
@[stacks 0F99]
theorem exists_principalReduction_isStableUnderBaseChange :
    ∃ R : PrincipalReduction C sX L s, R.IsStableUnderBaseChange :=
  ⟨principalReduction C sX L s,
    principalReductionOfDecomposition_isStableUnderBaseChange _ _ C sX L s _ _⟩

end Reduction

end TensorZeroScheme

end Stacks.Chow

end
