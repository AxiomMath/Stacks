module

public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemePower
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.SectionPowerThickenings

/-!
# The tower of zero schemes of the powers of a section

Let `X` be a scheme, `L` an invertible `𝒪_X`-module and `s` a global section of `L`. The zero
schemes `Z(sⁿ)` of the sectionwise powers of `s` form a decreasing tower of quasi-coherent ideal
sheaves, cutting out the infinitesimal neighbourhoods `Qₙ` of `Z(s)` that carry the comparison map
`Hⁱ(X, F) ⟶ lim Hⁱ(Qₙ, Fₙ)` of [Stacks, Tag 0EL1]. This is the tower as the source writes it, by
the zero schemes of the powers of `s`; `Stacks.Algebraization.zeroSchemeTowerIdeal` writes the same
tower as the powers `I ⁿ` of the ideal `I` of `Z(s)`, and the two agree by
`AlgebraicGeometry.zeroScheme_sectionPow'_degreeOne`.

## Main definitions

* `Stacks.Algebraization.sectionPowerTowerIdeal`: the tower `n ↦ Z(sⁿ)` of zero schemes of the
  sectionwise powers of `s`.
* `Stacks.Algebraization.sectionPowerThickening`, `sectionPowerThickeningι` and
  `sectionPowerThickeningMap`: the subschemes `Qₙ = Z(sⁿ)`, their closed immersions into `X` and
  the tower maps `Qₙ ⟶ Qₙ₊₁`.
* `Stacks.Algebraization.sectionPowerComparison`: the comparison map `Hⁱ(X, F) ⟶ lim Hⁱ(Qₙ, Fₙ)`
  for this tower.

## Main results

* `Stacks.Algebraization.sectionPowerTowerIdeal_eq`: `Z(sⁿ) = Z(s)ⁿ`.
* `Stacks.Algebraization.sectionPowerTowerIdeal_eq_zeroSchemeTowerIdeal`: the tower of zero
  schemes of the powers and the tower of powers of the ideal are the same function
  `ℕ → X.IdealSheafData`.
* `Stacks.Algebraization.IdealTower.cohomologyTower_congr` and
  `Stacks.Algebraization.IdealTower.comparison_comp_isoOfNatIso`: equal towers of ideal sheaves
  have equal cohomology towers, and their comparison maps agree under the induced isomorphism of
  limits.
* `Stacks.Algebraization.sectionPowerComparison_comp_isoOfNatIso`: the two comparison maps of
  [Stacks, Tag 0EL1] agree.

## Implementation notes

The exponent of the ambient module is `1 * n` rather than `n`: the sectionwise powers
`Stacks.SheafOfModules.Invertible.sectionPow'` of a global section of `L^{⊗ m}` land in
`L^{⊗ (m n)}`, and `s` enters in degree `m = 1` through
`Stacks.SheafOfModules.Invertible.sectionsDegreeOne`. The exponent sits inside the type of the
section, so `1 * n` is kept as it stands.

Two towers that are equal as functions have cohomology towers that are equal as functors, not
merely isomorphic: the decrease hypothesis `∀ n, Jₙ₊₁ ≤ Jₙ` is a proposition, so the two
instantiations differ only in a proof. The comparison maps then agree after composing with the
isomorphism of limits induced by that equality.

## References

* [Stacks Project, Tag 0EL1](https://stacks.math.columbia.edu/tag/0EL1)
* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.SheafOfModules Stacks.SheafOfModules.Invertible

namespace AlgebraicGeometry

/-- A tensor power of an invertible `𝒪_X`-module on a scheme is invertible in the spelling whose
presheaf of rings is written `X.toRingedSpace.presheaf`, the one the sectionwise powers of a
section are indexed by. The ringed-space statement is
`Stacks.SheafOfModules.Invertible.tensorPower_isInvertible`. -/
instance isInvertible_toRingedSpace_tensorPowerModule' (X : Scheme.{u}) (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (n : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property (tensorPowerModule' L n) :=
  Stacks.SheafOfModules.Invertible.tensorPower_isInvertible X.toRingedSpace.presheaf
    (structureSheafRing X.toRingedSpace).property L n

end AlgebraicGeometry

namespace Stacks.Algebraization

/-! ### Towers of ideal sheaves that are equal as functions -/

namespace IdealTower

variable {X : Scheme.{u}} {J J' : ℕ → X.IdealSheafData}

/-- Two towers of ideal sheaves that are equal as functions have equal cohomology towers. The
decrease hypotheses are propositions, so they contribute nothing beyond a proof. -/
theorem cohomologyTower_congr (hJ : ∀ n, J (n + 1) ≤ J n) (hJ' : ∀ n, J' (n + 1) ≤ J' n)
    (F : X.Modules) [F.IsQuasicoherent] (i : ℕ) (h : J = J') :
    cohomologyTower J hJ F i = cohomologyTower J' hJ' F i := by
  subst h; rfl

/-- The comparison maps of two towers of ideal sheaves that are equal as functions agree, under
the isomorphism of limits induced by the equality of their cohomology towers. -/
theorem comparison_comp_isoOfNatIso (hJ : ∀ n, J (n + 1) ≤ J n) (hJ' : ∀ n, J' (n + 1) ≤ J' n)
    (F : X.Modules) [F.IsQuasicoherent] (i : ℕ) (h : J = J') :
    comparison J hJ F i ≫ (HasLimit.isoOfNatIso
        (eqToIso (cohomologyTower_congr hJ hJ' F i h))).hom = comparison J' hJ' F i := by
  subst h
  refine limit.hom_ext fun n => ?_
  rw [Category.assoc, HasLimit.isoOfNatIso_hom_π]
  simp

end IdealTower

/-! ### The tower of zero schemes of the powers of a section -/

section SectionPower

variable (X : Scheme.{u}) (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] (s : Γ(L, ⊤))

/-- The tower `n ↦ Z(sⁿ)` of zero schemes of the sectionwise powers of a global section `s` of an
invertible module `L`, the `n`-th power being a global section of `L^{⊗ n}`. Its `n`-th subscheme
is the `n`-th infinitesimal neighbourhood of `Z(s)`, the `Qₙ` of [Stacks, Tag 0EL1]. -/
abbrev sectionPowerTowerIdeal (n : ℕ) : X.IdealSheafData :=
  zeroScheme X (tensorPowerModule' L ((1 * n : ℕ) : ℤ))
    ((sectionPow' L (sectionsDegreeOne L s) n).eval (op ⊤))

/-- **`Z(sⁿ) = Z(s)ⁿ`**: the zero scheme of the `n`-th power of `s` is cut out by the `n`-th power
of the ideal of `Z(s)`. -/
theorem sectionPowerTowerIdeal_eq (n : ℕ) :
    sectionPowerTowerIdeal X L s n = zeroSchemeTowerIdeal X L s n :=
  zeroScheme_sectionPow'_degreeOne L s n

/-- The tower of zero schemes of the powers of `s` and the tower of powers of the ideal of `Z(s)`
are the same function `ℕ → X.IdealSheafData`. -/
theorem sectionPowerTowerIdeal_eq_zeroSchemeTowerIdeal :
    sectionPowerTowerIdeal X L s = zeroSchemeTowerIdeal X L s :=
  funext (sectionPowerTowerIdeal_eq X L s)

/-- The zero schemes of the powers of `s` decrease at each step. -/
theorem sectionPowerTowerIdeal_succ_le (n : ℕ) :
    sectionPowerTowerIdeal X L s (n + 1) ≤ sectionPowerTowerIdeal X L s n :=
  sectionPowerTowerIdeal_eq_zeroSchemeTowerIdeal X L s ▸ zeroSchemeTowerIdeal_succ_le X L s n

/-- The zero schemes of the powers of `s` form a decreasing tower. -/
theorem antitone_sectionPowerTowerIdeal : Antitone (sectionPowerTowerIdeal X L s) :=
  antitone_nat_of_succ_le (sectionPowerTowerIdeal_succ_le X L s)

/-- The `n`-th infinitesimal neighbourhood `Qₙ = Z(sⁿ)` of the zero scheme of `s`. -/
abbrev sectionPowerThickening (n : ℕ) : Scheme.{u} :=
  IdealTower.scheme (sectionPowerTowerIdeal X L s) n

/-- The closed immersion `Z(sⁿ) ⟶ X`. -/
abbrev sectionPowerThickeningι (n : ℕ) : sectionPowerThickening X L s n ⟶ X :=
  IdealTower.ι (sectionPowerTowerIdeal X L s) n

/-- The tower map `Z(sⁿ) ⟶ Z(sⁿ⁺¹)`. -/
abbrev sectionPowerThickeningMap (n : ℕ) :
    sectionPowerThickening X L s n ⟶ sectionPowerThickening X L s (n + 1) :=
  IdealTower.map (sectionPowerTowerIdeal X L s) (sectionPowerTowerIdeal_succ_le X L s) n

/-- **The comparison map of [Stacks, Tag 0EL1]** along the tower of zero schemes of the powers of
`s`: `Hⁱ(X, F) ⟶ lim Hⁱ(Qₙ, Fₙ)` with `Qₙ = Z(sⁿ)` and `Fₙ` the restriction of `F` to it. -/
abbrev sectionPowerComparison (F : X.Modules) [F.IsQuasicoherent] (i : ℕ) :
    Hgroup X.ringCatSheaf ⊤ i F ⟶
      limit (IdealTower.cohomologyTower (sectionPowerTowerIdeal X L s)
        (sectionPowerTowerIdeal_succ_le X L s) F i) :=
  IdealTower.comparison (sectionPowerTowerIdeal X L s) (sectionPowerTowerIdeal_succ_le X L s) F i

/-- The cohomology tower along the zero schemes of the powers of `s` is the cohomology tower along
the powers of the ideal of `Z(s)`. -/
theorem cohomologyTower_sectionPowerTowerIdeal (F : X.Modules) [F.IsQuasicoherent] (i : ℕ) :
    IdealTower.cohomologyTower (sectionPowerTowerIdeal X L s)
        (sectionPowerTowerIdeal_succ_le X L s) F i =
      IdealTower.cohomologyTower (zeroSchemeTowerIdeal X L s)
        (zeroSchemeTowerIdeal_succ_le X L s) F i :=
  IdealTower.cohomologyTower_congr _ _ F i (sectionPowerTowerIdeal_eq_zeroSchemeTowerIdeal X L s)

/-- The comparison map along the zero schemes of the powers of `s` is the comparison map along the
powers of the ideal of `Z(s)`, under the induced isomorphism of limits. -/
theorem sectionPowerComparison_comp_isoOfNatIso (F : X.Modules) [F.IsQuasicoherent] (i : ℕ) :
    sectionPowerComparison X L s F i ≫ (HasLimit.isoOfNatIso
        (eqToIso (cohomologyTower_sectionPowerTowerIdeal X L s F i))).hom =
      zeroSchemeComparison X L s F i :=
  IdealTower.comparison_comp_isoOfNatIso _ _ F i
    (sectionPowerTowerIdeal_eq_zeroSchemeTowerIdeal X L s)

end SectionPower

end Stacks.Algebraization

end
