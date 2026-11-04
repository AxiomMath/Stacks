module

public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicOrder.Stalk
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierAffineLocal
public import StacksFrontier.AlgebraicGeometry.GenericPointSheaf.StalkUnits
public import StacksFrontier.AlgebraicGeometry.InvertibleTrivialization.Basic
public import StacksFrontier.AlgebraicGeometry.Meromorphic.DenominatorSupport

/-!
# A regular meromorphic section near a generic point of an irreducible component

Let `X` be a scheme, `L` an invertible `𝒪_X`-module and `s` a *regular* meromorphic section of
`L` in the sense of [Tag 02OX](https://stacks.math.columbia.edu/tag/02OX). This file proves that
near a generic point of an irreducible component of `X` the section `s` is the meromorphic image
of an honest section of `L` whose germ there is a *basis* of the stalk.

That is the local input to [Tag 02OY](https://stacks.math.columbia.edu/tag/02OY) part (2), the
regularity of a pullback: it is what makes the germ of the pulled-back section nonzero.

## Main results

* `Stacks.Divisors.surjective_smul_germ_of_surjective_smul`: sectionwise generation by a section
  gives stalkwise generation by its germ.
* `Stacks.Divisors.IsStalkBasis.of_surjective_smul`: a generator of a free rank one stalk is a
  basis.
* `Stacks.Divisors.exists_isStalkBasis_germ_of_isInvertible`: an invertible module has a stalk
  basis at every point. This is the converse half of
  [Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M) read on one stalk.
* `AlgebraicGeometry.exists_isStalkBasis_toMeromorphicSectionSheafAsModule_eq`: **near a generic
  point of an irreducible component a regular meromorphic section of an invertible module is the
  meromorphic image of a section whose germ is a stalk basis.**

## Implementation notes

The last result sharpens `AlgebraicGeometry.exists_isAffineOpen_nhds_denominator_numerator`,
which puts `s` in the normal form `b · s = a · g` on an affine open with `b` a nonzerodivisor,
`g` a generator of `L` there, and — by
`AlgebraicGeometry.numerator_mem_nonZeroDivisors`, the only use of regularity — the numerator `a`
a nonzerodivisor as well. At a generic point of an irreducible component the local ring has
dimension zero, so a nonzerodivisor germ is a unit
(`Stacks.AlgebraicGeometry.GenericPointSheaf.isUnit_of_mem_nonZeroDivisors_stalk`); hence the
germs of both `a` and `b` are units. Shrinking to the basic open set of `b` makes `b` invertible
on sections, so there `s` is the meromorphic image of `(b⁻¹ a) · g`, and the germ of that is a
unit multiple of the germ of `g`.

That the germ of `g` is a stalk *basis* and not merely a generator is the only place
invertibility of `L` is used a second time: the normal form keeps only surjectivity of
multiplication by `g`, so the germ of `g` is compared with the honest basis that
`exists_isStalkBasis_germ_of_isInvertible` supplies, and
`Stacks.Divisors.IsStalkBasis.of_surjective_smul` upgrades it.

Three spellings of a germ of a module meet in this area of the tree. Everything below is kept in
the `AlgebraicGeometry.Scheme.Modules` one, in which `Stacks.Divisors.IsStalkBasis` is stated:
the `Stacks.SheafOfModules.TensorStalkRingedSpace.grpGerm` spelling carries a *different* module
structure on the stalk, equal only by `Stacks.SheafOfModules.stalkModule_eq` and not at the
transparency a `Function.Bijective` motive uses, so invertibility is read through the
*sectionwise* bijectivity of
`Stacks.SheafOfModules.exists_bijective_smul_of_isInvertible` and
`Stacks.Divisors.isStalkBasis_germ_of_bijective_smul`, where only one module structure exists.

## References

* [Stacks Project, Tag 02OX](https://stacks.math.columbia.edu/tag/02OX)
* [Stacks Project, Tag 02OY](https://stacks.math.columbia.edu/tag/02OY)
* [Stacks Project, Tag 02P0](https://stacks.math.columbia.edu/tag/02P0)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open scoped nonZeroDivisors

universe u

namespace Stacks.Divisors

/-! ### Stalk bases from sectionwise generation -/

/-- **Sectionwise generation by a section gives stalkwise generation by its germ.** If
multiplication by `e` is surjective on the sections over every open set inside its domain, then
multiplication by the germ of `e` is surjective on the stalk at every point of that domain.

This is the surjective half of `Stacks.Divisors.isStalkBasis_germ_of_bijective_smul`, whose
bijective hypothesis is not always available: the generator produced by
`AlgebraicGeometry.exists_isAffineOpen_nhds_denominator_numerator` carries only surjectivity. -/
theorem surjective_smul_germ_of_surjective_smul {X : Scheme.{u}} (L : X.Modules)
    {W : X.Opens} (e : Γ(L, W))
    (h : ∀ V : X.Opens, ∀ hV : V ≤ W,
      Function.Surjective fun c : Γ(X, V) => c • L.presheaf.map (homOfLE hV).op e)
    (y : X) (hy : y ∈ W) :
    Function.Surjective fun r : X.presheaf.stalk y => r • L.presheaf.germ W y hy e := by
  intro m
  obtain ⟨V, hVW, hyV, g, hg⟩ := L.presheaf.exists_le_germ_eq m hy
  obtain ⟨c, hc⟩ := h V hVW g
  replace hc : c • L.presheaf.map (homOfLE hVW).op e = g := hc
  refine ⟨X.presheaf.germ V y hyV c, ?_⟩
  show X.presheaf.germ V y hyV c • L.presheaf.germ W y hy e = m
  rw [← L.presheaf.germ_res_apply (homOfLE hVW) y hyV e, ← Scheme.Modules.germ_smul L hyV, hc, hg]

/-- **A generator of a free rank one stalk is a basis.** If some element of the stalk is a stalk
basis and multiplication by `m'` is surjective, then `m'` is a stalk basis too: `m'` is a
multiple of the basis by a scalar which the surjectivity makes invertible. -/
theorem IsStalkBasis.of_surjective_smul {X : Scheme.{u}} {L : X.Modules} {y : X}
    {m m' : L.presheaf.stalk y} (hm : IsStalkBasis L y m)
    (hsurj : Function.Surjective fun r : X.presheaf.stalk y => r • m') :
    IsStalkBasis L y m' := by
  obtain ⟨c, hc⟩ := hm.surjective m'
  replace hc : c • m = m' := hc
  obtain ⟨d, hd⟩ := hsurj m
  replace hd : d • m' = m := hd
  have key : (d * c) • m = (1 : X.presheaf.stalk y) • m := by
    rw [mul_smul, hc, hd, one_smul]
  have hdc : d * c = 1 := hm.injective key
  rw [← hc]
  exact hm.smul_of_isUnit (isUnit_iff_exists.mpr ⟨d, by rw [mul_comm]; exact hdc, hdc⟩)

/-- **An invertible module has a stalk basis at every point**, the converse half of
[Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M) read on one stalk. It is obtained from the
sectionwise bijectivity that `Stacks.SheafOfModules.exists_bijective_smul_of_isInvertible`
supplies, so that the stalk module structure never has to be transported. -/
theorem exists_isStalkBasis_germ_of_isInvertible {Y : Scheme.{u}} (L : Y.Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L)
    (y : Y) :
    ∃ (W : Y.Opens) (hy : y ∈ W) (a : Γ(L, W)), IsStalkBasis L y (L.presheaf.germ W y hy a) := by
  have hloc : ∀ z : Y.toRingedSpace.carrier,
      IsLocalRing (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk Y.toRingedSpace z) :=
    fun z => Y.isLocalRing z
  have hinv : Stacks.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf
      (structureSheafRing
        Y.toRingedSpace).property L :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ L).mpr hL
  obtain ⟨W, hy, a, hbij⟩ := Stacks.SheafOfModules.exists_bijective_smul_of_isInvertible
    (X := Y.toRingedSpace) L y
  exact ⟨W, hy, a, isStalkBasis_germ_of_bijective_smul a (fun V hV => hbij V hV) y hy⟩

end Stacks.Divisors

namespace AlgebraicGeometry

/-! ### The local normal form at a generic point -/

/-- Multiplication by a meromorphic section, read on the sections over an open set: it is the
scalar action, typed at the sheaf of meromorphic sections regarded as an `𝒪_X`-module. -/
private theorem meromorphicSectionMul_app_apply (Y : Scheme.{u}) (L : Y.Modules)
    (s : MeromorphicSection Y.sheaf L) (V : (Opens Y)ᵒᵖ)
    (c : (Stacks.Sheaves.Differentials.ringSheaf
      (J := Opens.grothendieckTopology Y) Y.sheaf).obj.obj V) :
    ((meromorphicSectionMul Y L s).val.app V).hom c =
      c • (show (meromorphicSectionSheafAsModule Y L).val.obj V from s.eval V) := rfl

/-- Restriction of sections is semilinear, in the spelling the denominator lemmas state the
normal form `b · s = a · g` in. Both the scalar and the section are restricted inside that
spelling: writing the restricted scalar as `Y.presheaf.map`, which is the same element read in
`CommRingCat`, makes the defeq check between the two module structures on the sections blow
past the heartbeat limit. -/
private theorem restrictₛₗ_smul (Y : Scheme.{u}) (L : Y.Modules) {V W : Y.Opens} (h : V ≤ W)
    (a : (Stacks.Sheaves.Differentials.ringSheaf
      (J := Opens.grothendieckTopology Y) Y.sheaf).obj.obj (op W))
    (g : L.val.obj (op W)) :
    (L.val.restrictₛₗ (homOfLE h).op (a • g) : L.val.obj (op V)) =
      ((Stacks.Sheaves.Differentials.ringSheaf
        (J := Opens.grothendieckTopology Y) Y.sheaf).obj.map (homOfLE h).op).hom a •
        (L.val.restrictₛₗ (homOfLE h).op g : L.val.obj (op V)) :=
  L.val.map_smul _ _ _

/-- **A regular meromorphic section with an invertible denominator is an honest section.** If
`b · s = a · g` over `V` with `b` invertible on the sections over `V`, then `s` is over `V` the
meromorphic image of `(b⁻¹ a) · g`; and if moreover the germ of `a` at `y` is a unit of the local
ring and the germ of `g` is a stalk basis, then so is the germ of that section.

Stated over an abstract open set and abstract sections, with no restriction map in it: the two
module structures on the sections of `L` are then never compared under a restriction, which is
what makes this elaborate at all. -/
private theorem exists_isStalkBasis_of_isUnit_denominator (Y : Scheme.{u}) (L : Y.Modules)
    (s : MeromorphicSection Y.sheaf L) {y : Y} {V : Y.Opens} (hyV : y ∈ V)
    {b : (Stacks.Sheaves.Differentials.ringSheaf
      (J := Opens.grothendieckTopology Y) Y.sheaf).obj.obj (op V)} (hb : IsUnit b)
    (a : (Stacks.Sheaves.Differentials.ringSheaf
      (J := Opens.grothendieckTopology Y) Y.sheaf).obj.obj (op V))
    (g : L.val.obj (op V))
    (heq : ((meromorphicSectionMul Y L s).val.app (op V)).hom b =
      ((toMeromorphicSectionSheafAsModule Y L).val.app (op V)).hom (a • g))
    (hga : IsUnit (Y.presheaf.germ V y hyV (show Γ(Y, V) from a)))
    (hbasg : Stacks.Divisors.IsStalkBasis L y (L.presheaf.germ V y hyV (show Γ(L, V) from g))) :
    ∃ t : L.val.obj (op V),
      ((toMeromorphicSectionSheafAsModule Y L).val.app (op V)).hom t = s.val (op V) ∧
        Stacks.Divisors.IsStalkBasis L y
          (L.presheaf.germ V y hyV (show Γ(L, V) from t)) := by
  obtain ⟨c₀, hc₀⟩ := hb.exists_left_inv
  refine ⟨(c₀ * a) • g, ?_, ?_⟩
  · -- `s` is the meromorphic image of `(b⁻¹ a) · g`
    have h1 : ((toMeromorphicSectionSheafAsModule Y L).val.app (op V)).hom ((c₀ * a) • g) =
        c₀ • ((toMeromorphicSectionSheafAsModule Y L).val.app (op V)).hom (a • g) := by
      rw [mul_smul]
      exact ((toMeromorphicSectionSheafAsModule Y L).val.app (op V)).hom.map_smul c₀ _
    rw [h1, ← heq, meromorphicSectionMul_app_apply Y L s (op V) b, smul_smul, hc₀, one_smul]
  · -- its germ is a unit multiple of the germ of `g`, hence a stalk basis
    have hc₀' : (show Γ(Y, V) from c₀) * (show Γ(Y, V) from b) = 1 := hc₀
    have hgc₀ : IsUnit (Y.presheaf.germ V y hyV (show Γ(Y, V) from c₀)) := by
      refine IsUnit.of_mul_eq_one (Y.presheaf.germ V y hyV (show Γ(Y, V) from b)) ?_
      rw [← map_mul, hc₀', map_one]
    have hmulbridge : (show Γ(Y, V) from c₀ * a) =
        (show Γ(Y, V) from c₀) * (show Γ(Y, V) from a) := rfl
    have hunit : IsUnit (Y.presheaf.germ V y hyV (show Γ(Y, V) from c₀ * a)) := by
      rw [hmulbridge, map_mul]
      exact hgc₀.mul hga
    have hsmulbridge : (show Γ(L, V) from (c₀ * a) • g) =
        (show Γ(Y, V) from c₀ * a) • (show Γ(L, V) from g) := rfl
    rw [hsmulbridge, Scheme.Modules.germ_smul L hyV]
    exact hbasg.smul_of_isUnit hunit

/-- **Near a generic point of an irreducible component a regular meromorphic section of an
invertible module is the meromorphic image of a section whose germ is a stalk basis.**

The normal form `b · s = a · g` of
`AlgebraicGeometry.exists_isAffineOpen_nhds_denominator_numerator` has `b` a nonzerodivisor on an
affine open, and regularity of `s` makes the numerator `a` one as well. The local ring at a
generic point of an irreducible component has dimension zero, so both germs are units; shrinking
to the basic open set of `b` makes `b` invertible on sections, and `s` is there the meromorphic
image of `(b⁻¹ a) · g`, whose germ is a unit multiple of the germ of `g`. -/
theorem exists_isStalkBasis_toMeromorphicSectionSheafAsModule_eq (Y : Scheme.{u})
    (L : Y.Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L)
    (s : MeromorphicSection Y.sheaf L) (hs : IsRegularMeromorphicSection Y.sheaf L s)
    {y : Y} (hy : y ∈ genericPoints Y) :
    ∃ (V : Y.Opens) (hyV : y ∈ V) (t : L.val.obj (op V)),
      ((toMeromorphicSectionSheafAsModule Y L).val.app (op V)).hom t = s.val (op V) ∧
        Stacks.Divisors.IsStalkBasis L y
          (L.presheaf.germ V y hyV (show Γ(L, V) from t)) := by
  obtain ⟨V₀, hyV₀, hV₀, g, hgsurj, b, hb, a, heq⟩ :=
    exists_isAffineOpen_nhds_denominator_numerator Y L s hL y
  have ha : (show Γ(Y, V₀) from a) ∈ (Γ(Y, V₀))⁰ :=
    numerator_mem_nonZeroDivisors Y L s hs hb heq
  -- the germs at `y` of the denominator and of the numerator are units
  have hunit : ∀ x : Γ(Y, V₀), x ∈ (Γ(Y, V₀))⁰ → IsUnit (Y.presheaf.germ V₀ y hyV₀ x) :=
    fun x hx => Stacks.AlgebraicGeometry.GenericPointSheaf.isUnit_of_mem_nonZeroDivisors_stalk hy
      (Stacks.Divisors.germ_mem_nonZeroDivisors hV₀
        (isRegular_iff_mem_nonZeroDivisors.mpr hx) y hyV₀)
  -- the germ of the generator is a stalk basis, not merely a generator
  obtain ⟨_, _, _, hbas₁⟩ := Stacks.Divisors.exists_isStalkBasis_germ_of_isInvertible L hL y
  have hbas := hbas₁.of_surjective_smul
    (Stacks.Divisors.surjective_smul_germ_of_surjective_smul L (show Γ(L, V₀) from g)
      (fun U hU => hgsurj U hU) y hyV₀)
  -- shrink to the basic open set of the denominator, where it is invertible
  have hyb : y ∈ Y.basicOpen b := (Y.mem_basicOpen b y hyV₀).mpr (hunit b hb)
  have hVV₀ : V₀ ⊓ Y.basicOpen b ≤ V₀ := inf_le_left
  have hyV : y ∈ V₀ ⊓ Y.basicOpen b := ⟨hyV₀, hyb⟩
  have heq2 : ((meromorphicSectionMul Y L s).val.app (op (V₀ ⊓ Y.basicOpen b))).hom
        ((Y.presheaf.map (homOfLE hVV₀).op).hom b) =
      ((toMeromorphicSectionSheafAsModule Y L).val.app (op (V₀ ⊓ Y.basicOpen b))).hom
        (((Stacks.Sheaves.Differentials.ringSheaf
            (J := Opens.grothendieckTopology Y) Y.sheaf).obj.map (homOfLE hVV₀).op).hom a •
          (L.val.restrictₛₗ (homOfLE hVV₀).op g : L.val.obj (op (V₀ ⊓ Y.basicOpen b)))) :=
    (meromorphicSectionMul_app_res_eq Y L s hVV₀ b (a • g) heq).trans
      (congrArg (fun z => ((toMeromorphicSectionSheafAsModule Y L).val.app
        (op (V₀ ⊓ Y.basicOpen b))).hom z) (restrictₛₗ_smul Y L hVV₀ a g))
  have hgermg : L.presheaf.germ (V₀ ⊓ Y.basicOpen b) y hyV
        (show Γ(L, V₀ ⊓ Y.basicOpen b) from
          (L.val.restrictₛₗ (homOfLE hVV₀).op g : L.val.obj (op (V₀ ⊓ Y.basicOpen b)))) =
      L.presheaf.germ V₀ y hyV₀ (show Γ(L, V₀) from g) :=
    L.presheaf.germ_res_apply (homOfLE hVV₀) y hyV (show Γ(L, V₀) from g)
  have hgerma : Y.presheaf.germ (V₀ ⊓ Y.basicOpen b) y hyV
        (show Γ(Y, V₀ ⊓ Y.basicOpen b) from
          ((Stacks.Sheaves.Differentials.ringSheaf
            (J := Opens.grothendieckTopology Y) Y.sheaf).obj.map (homOfLE hVV₀).op).hom a) =
      Y.presheaf.germ V₀ y hyV₀ (show Γ(Y, V₀) from a) :=
    Y.presheaf.germ_res_apply (homOfLE hVV₀) y hyV (show Γ(Y, V₀) from a)
  obtain ⟨t, ht1, ht2⟩ := exists_isStalkBasis_of_isUnit_denominator Y L s hyV
    (b := (Y.presheaf.map (homOfLE hVV₀).op).hom b)
    (isUnit_presheaf_map_of_le_basicOpen Y b inf_le_right hVV₀)
    (((Stacks.Sheaves.Differentials.ringSheaf
      (J := Opens.grothendieckTopology Y) Y.sheaf).obj.map (homOfLE hVV₀).op).hom a)
    (L.val.restrictₛₗ (homOfLE hVV₀).op g) heq2
    (by rw [hgerma]; exact hunit _ ha) (by rw [hgermg]; exact hbas)
  exact ⟨V₀ ⊓ Y.basicOpen b, hyV, t, ht1, ht2⟩

end AlgebraicGeometry

end
