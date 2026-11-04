module

public import StacksFrontier.AlgebraicGeometry.Blowup.AdmissibleDominating
public import StacksFrontier.AlgebraicGeometry.Blowup.ExceptionalDifferentials
public import StacksFrontier.AlgebraicGeometry.Divisors.DeterminantTwistBoundDivisorQuotient
public import StacksFrontier.AlgebraicGeometry.Divisors.DivisorPicardClass

/-!
# The top forms of a blowup differ from the pulled-back top forms by a bounded twist

Let `X` be an integral regular scheme of dimension at most two, let `b : X ⟶ S` be a morphism
whose relative differentials are carried by an integral effective Cartier divisor `i : D ⟶ X`,

`Ω_{X/S} ≅ i_*𝒢` with `𝒢` finite locally free of rank `s` on `D`,

and let `q : S ⟶ S₀`. Write `Ω^r = (⋀^r Ω)^{∨∨}` for the reflexive hull of the top exterior
power. The fundamental right-exact sequence of the tower `X ⟶ S ⟶ S₀`,

`b^*Ω_{S/S₀} ⟶ Ω_{X/S₀} ⟶ Ω_{X/S} ⟶ 0`,

then has a last term of the shape [Stacks, Tag 0B3T] asks for, and the conclusion of that tag
reads

`(⋀^r Ω_{X/S₀})^{∨∨} ≅ ((⋀^r b^*Ω_{S/S₀})^{∨∨})(kD)` for some `k ≤ min s r`.

For a blowup `b : X ⟶ S` in the ideal of a closed immersion the hypothesis on `Ω_{X/S}` is
[Stacks, Tag 0B4L]: the relative differentials of a blowup are the direct image of the relative
differentials of its exceptional divisor over the centre. With `s = 1` — the case in which the
exceptional divisor is a curve and its differentials over the centre are invertible — the bound
is `k ≤ 1`, which is the dichotomy

`Ω^r_X ≅ (b^*Ω^r_S)(E)` or `Ω^r_X ≅ b^*Ω^r_S`

used in the inductive step of [Stacks, Tag 0B4T].

## Main results

* `Stacks.BlowupFormsDichotomy.exists_le_min_tensorIso_reflexiveHull_exteriorPower_of_forms_iso`:
  the bounded twist for a morphism whose relative differentials are carried by a divisor.
* `Stacks.BlowupFormsDichotomy.exists_le_min_tensorIso_reflexiveHull_exteriorPower_blowUp`: its
  instance at a blowup, where the hypothesis on `Ω_{X/S}` is supplied by [Stacks, Tag 0B4L].
* `Stacks.BlowupFormsDichotomy.exists_eq_zero_or_eq_one_tensorIso_reflexiveHull_exteriorPower`:
  the dichotomy itself — for `s = 1` the twist exponent is `0` or `1`.
* `Stacks.BlowupFormsDichotomy.nonempty_tensorIso_or_nonempty_iso_reflexiveHull_exteriorPower`:
  the same with the two alternatives spelled out, the twist by `0 · E` having been removed.

## Implementation notes

*Why the first theorem does not mention a blowup.* The only property of a blowup the argument
uses is that its relative differentials over the centre are the direct image of a finite locally
free module on an effective Cartier divisor. Keeping that as a hypothesis makes the result
available to each of the library's constructions of the blowup, which are isomorphic over the
base (`Stacks.Blowup.blowUpIso`) but not definitionally equal; the second theorem instantiates it
at the construction on which [Stacks, Tag 0B4L] is stated.

*The shape of the pulled-back term.* The twist is measured against
`(⋀^r b^*Ω_{S/S₀})^{∨∨}`, the reflexive hull of the top exterior power of the pullback, which is
what the right-exact sequence provides. Identifying it with `b^*((⋀^r Ω_{S/S₀})^{∨∨})`, the
pullback of the determinant downstairs, is a separate step and is not carried out here.

## References

* [Stacks Project, Tag 0B3T](https://stacks.math.columbia.edu/tag/0B3T)
* [Stacks Project, Tag 0B4L](https://stacks.math.columbia.edu/tag/0B4L)
* [Stacks Project, Tag 0B4T](https://stacks.math.columbia.edu/tag/0B4T)
* [Stacks Project, Tag 01UX](https://stacks.math.columbia.edu/tag/01UX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.AlgebraicGeometry.ReflexiveModules
open Scheme.Modules Stacks.SheafOfModules

universe u

namespace Stacks.BlowupFormsDichotomy

/-- **The top forms of `X` over `S₀` differ from the pulled-back top forms of `S` by at most
`min s r` copies of a divisor carrying `Ω_{X/S}`.**

Let `X` be an integral regular scheme of dimension at most two, let `i : D ⟶ X` be an integral
effective Cartier divisor, and let `b : X ⟶ S` be a morphism whose relative differentials are the
direct image `i_*𝒢` of a module `𝒢` finite locally free of rank `s` on `D`. Let `q : S ⟶ S₀` and
suppose `b^*Ω_{S/S₀}` and `Ω_{X/S₀}` are coherent and both of rank `r` on a nonempty open. Then

`((⋀^r b^*Ω_{S/S₀})^{∨∨})(kD) ≅ (⋀^r Ω_{X/S₀})^{∨∨}` for some `k ≤ min s r`.

The right-exact sequence `b^*Ω_{S/S₀} ⟶ Ω_{X/S₀} ⟶ Ω_{X/S} ⟶ 0` of [Stacks, Tag 01UX] has last
term `i_*𝒢`, so [Stacks, Tag 0B3T] applies to it verbatim; this is the use [Stacks, Tag 0B4T]
makes of that tag. -/
theorem exists_le_min_tensorIso_reflexiveHull_exteriorPower_of_forms_iso
    {X S S₀ : Scheme.{u}} (b : X ⟶ S) (q : S ⟶ S₀)
    [IsIntegral X] (hX : AlgebraicGeometry.IsRegular X)
    (hXdim : topologicalKrullDim X ≤ 2)
    (D : X.IdealSheafData) (hD : Stacks.Divisors.IsEffectiveCartierDivisor D)
    [IsIntegral D.subscheme]
    (G : D.subscheme.Modules) (s : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} G s]
    (hforms : Scheme.Hom.relativeDifferentials b ≅
      (Scheme.Modules.pushforward D.subschemeι).obj G)
    (r : ℕ)
    [((Scheme.Modules.pullback b).obj (Scheme.Hom.relativeDifferentials q)).IsCoherent]
    [(Scheme.Hom.relativeDifferentials (b ≫ q)).IsCoherent]
    (U : X.Opens) (hU : ∃ x : X, x ∈ U)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (((Scheme.Modules.pullback b).obj (Scheme.Hom.relativeDifferentials q)).over U) r]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Hom.relativeDifferentials (b ≫ q)).over U) r] :
    ∃ k : ℕ, k ≤ min s r ∧ Nonempty
      (((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨X.sheaf.obj,
              Presheaf.isSheaf_of_isSheaf_comp _ X.sheaf.obj
                (forget₂ CommRingCat RingCat) X.ringCatSheaf.property⟩).obj
          (Stacks.Divisors.invertibleSheaf' (D ^ k))).obj
        (reflexiveHull (exteriorPower
          ((Scheme.Modules.pullback b).obj (Scheme.Hom.relativeDifferentials q)) (r : ℤ))) ≅
      reflexiveHull (exteriorPower (Scheme.Hom.relativeDifferentials (b ≫ q)) (r : ℤ))) := by
  obtain ⟨hzero, hexact⟩ := Scheme.Hom.toRelativeDifferentials_exact b q
  have : Epi (b.toRelativeDifferentials q) := Scheme.Hom.toRelativeDifferentials_epi _ _
  exact AlgebraicGeometry.exists_reflexiveHull_exteriorPower_iso_tensor_cartier
    X hX hXdim D hD G s (ShortComplex.mk _ _ hzero) hexact hforms r U hU

/-- **The top forms of a blowup differ from the pulled-back top forms of the base by at most
`min s r` copies of the exceptional divisor.**

Let `p : Z ⟶ S` be a closed immersion, let `b : X ⟶ S` be the blowing up of `S` in `ker p` and
let `i : E ⟶ X` be its exceptional divisor, assumed integral; assume `X` integral and regular of
dimension at most two. Let `Ω_{E/Z}` be finite locally free of rank `s` on `E`, let `q : S ⟶ S₀`,
and assume the generic-rank and coherence hypotheses of
`Stacks.BlowupFormsDichotomy.exists_le_min_tensorIso_reflexiveHull_exteriorPower_of_forms_iso`.
Then

`((⋀^r b^*Ω_{S/S₀})^{∨∨})(kE) ≅ (⋀^r Ω_{X/S₀})^{∨∨}` for some `k ≤ min s r`.

The exceptional divisor is an effective Cartier divisor by [Stacks, Tag 02OS], and
`Ω_{X/S} ≅ i_*Ω_{E/Z}` is [Stacks, Tag 0B4L]; nothing else about the blowup is used. -/
theorem exists_le_min_tensorIso_reflexiveHull_exteriorPower_blowUp
    {S Z S₀ : Scheme.{u}} (p : Z ⟶ S) [IsClosedImmersion p] (q : S ⟶ S₀)
    [IsIntegral (Stacks.Blowup.blowUp p.ker)]
    (hX : AlgebraicGeometry.IsRegular (Stacks.Blowup.blowUp p.ker))
    (hXdim : topologicalKrullDim (Stacks.Blowup.blowUp p.ker) ≤ 2)
    [IsIntegral (Stacks.Blowup.exceptionalIdeal p.ker).subscheme]
    (s : ℕ)
    (hE : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (show ((Stacks.Blowup.exceptionalIdeal p.ker).subscheme).Modules from
        Scheme.Hom.relativeDifferentials (Stacks.Blowup.exceptionalToCentre p)) s)
    (r : ℕ)
    [((Scheme.Modules.pullback (Stacks.Blowup.blowUpToBase p.ker)).obj
        (Scheme.Hom.relativeDifferentials q)).IsCoherent]
    [(Scheme.Hom.relativeDifferentials
        (Stacks.Blowup.blowUpToBase p.ker ≫ q)).IsCoherent]
    (U : (Stacks.Blowup.blowUp p.ker).Opens)
    (hU : ∃ x : Stacks.Blowup.blowUp p.ker, x ∈ U)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (((Scheme.Modules.pullback (Stacks.Blowup.blowUpToBase p.ker)).obj
        (Scheme.Hom.relativeDifferentials q)).over U) r]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Hom.relativeDifferentials
        (Stacks.Blowup.blowUpToBase p.ker ≫ q)).over U) r] :
    ∃ k : ℕ, k ≤ min s r ∧ Nonempty
      (((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨(Stacks.Blowup.blowUp p.ker).sheaf.obj,
              Presheaf.isSheaf_of_isSheaf_comp _ (Stacks.Blowup.blowUp p.ker).sheaf.obj
                (forget₂ CommRingCat RingCat)
                (Stacks.Blowup.blowUp p.ker).ringCatSheaf.property⟩).obj
          (Stacks.Divisors.invertibleSheaf' (Stacks.Blowup.exceptionalIdeal p.ker ^ k))).obj
        (reflexiveHull (exteriorPower ((Scheme.Modules.pullback
          (Stacks.Blowup.blowUpToBase p.ker)).obj
            (Scheme.Hom.relativeDifferentials q)) (r : ℤ))) ≅
      reflexiveHull (exteriorPower (Scheme.Hom.relativeDifferentials
        (Stacks.Blowup.blowUpToBase p.ker ≫ q)) (r : ℤ))) := by
  have := Stacks.Blowup.isIso_relativeDifferentialsToPushforward p
  have := hE
  exact exists_le_min_tensorIso_reflexiveHull_exteriorPower_of_forms_iso
    (Stacks.Blowup.blowUpToBase p.ker) q hX hXdim (Stacks.Blowup.exceptionalIdeal p.ker)
    (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal_reesData p.ker)
    (show ((Stacks.Blowup.exceptionalIdeal p.ker).subscheme).Modules from
      Scheme.Hom.relativeDifferentials (Stacks.Blowup.exceptionalToCentre p)) s
    (asIso (Stacks.Blowup.relativeDifferentialsToPushforward p)) r U hU

/-- **The dichotomy of [Stacks, Tag 0B4T]: the twist exponent of a point blowup is `0` or `1`.**

In the situation of
`Stacks.BlowupFormsDichotomy.exists_le_min_tensorIso_reflexiveHull_exteriorPower_blowUp` with
`Ω_{E/Z}` invertible — finite locally free of rank one, the case of a blowup whose exceptional
divisor is a curve — the bound `k ≤ min 1 r` leaves only two possibilities, so

`Ω^r_X ≅ (b^*Ω^r_S)(E)` or `Ω^r_X ≅ b^*Ω^r_S`,

the first alternative being `k = 1` and the second `k = 0`. -/
theorem exists_eq_zero_or_eq_one_tensorIso_reflexiveHull_exteriorPower
    {S Z S₀ : Scheme.{u}} (p : Z ⟶ S) [IsClosedImmersion p] (q : S ⟶ S₀)
    [IsIntegral (Stacks.Blowup.blowUp p.ker)]
    (hX : AlgebraicGeometry.IsRegular (Stacks.Blowup.blowUp p.ker))
    (hXdim : topologicalKrullDim (Stacks.Blowup.blowUp p.ker) ≤ 2)
    [IsIntegral (Stacks.Blowup.exceptionalIdeal p.ker).subscheme]
    (hE : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (show ((Stacks.Blowup.exceptionalIdeal p.ker).subscheme).Modules from
        Scheme.Hom.relativeDifferentials (Stacks.Blowup.exceptionalToCentre p)) 1)
    (r : ℕ)
    [((Scheme.Modules.pullback (Stacks.Blowup.blowUpToBase p.ker)).obj
        (Scheme.Hom.relativeDifferentials q)).IsCoherent]
    [(Scheme.Hom.relativeDifferentials
        (Stacks.Blowup.blowUpToBase p.ker ≫ q)).IsCoherent]
    (U : (Stacks.Blowup.blowUp p.ker).Opens)
    (hU : ∃ x : Stacks.Blowup.blowUp p.ker, x ∈ U)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (((Scheme.Modules.pullback (Stacks.Blowup.blowUpToBase p.ker)).obj
        (Scheme.Hom.relativeDifferentials q)).over U) r]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Hom.relativeDifferentials
        (Stacks.Blowup.blowUpToBase p.ker ≫ q)).over U) r] :
    ∃ k : ℕ, (k = 0 ∨ k = 1) ∧ Nonempty
      (((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨(Stacks.Blowup.blowUp p.ker).sheaf.obj,
              Presheaf.isSheaf_of_isSheaf_comp _ (Stacks.Blowup.blowUp p.ker).sheaf.obj
                (forget₂ CommRingCat RingCat)
                (Stacks.Blowup.blowUp p.ker).ringCatSheaf.property⟩).obj
          (Stacks.Divisors.invertibleSheaf' (Stacks.Blowup.exceptionalIdeal p.ker ^ k))).obj
        (reflexiveHull (exteriorPower ((Scheme.Modules.pullback
          (Stacks.Blowup.blowUpToBase p.ker)).obj
            (Scheme.Hom.relativeDifferentials q)) (r : ℤ))) ≅
      reflexiveHull (exteriorPower (Scheme.Hom.relativeDifferentials
        (Stacks.Blowup.blowUpToBase p.ker ≫ q)) (r : ℤ))) := by
  obtain ⟨k, hk, hiso⟩ := exists_le_min_tensorIso_reflexiveHull_exteriorPower_blowUp
    p q hX hXdim 1 hE r U hU
  exact ⟨k, Nat.le_one_iff_eq_zero_or_eq_one.mp (hk.trans (min_le_left _ _)), hiso⟩

/-- **The dichotomy of [Stacks, Tag 0B4T] with its two alternatives spelled out.**

In the situation of
`Stacks.BlowupFormsDichotomy.exists_le_min_tensorIso_reflexiveHull_exteriorPower_blowUp` with
`Ω_{E/Z}` invertible,

`Ω^r_X ≅ (b^*Ω^r_S)(E)` or `Ω^r_X ≅ b^*Ω^r_S`,

where `Ω^r` abbreviates `(⋀^r Ω)^{∨∨}` and `b^*Ω^r_S` is the hull of the top exterior power of
`b^*Ω_{S/S₀}`. The first alternative is the twist exponent `k = 1`, the second `k = 0`, in which
case `𝒪_X(0 · E)` is the structure sheaf and the twist disappears. -/
theorem nonempty_tensorIso_or_nonempty_iso_reflexiveHull_exteriorPower
    {S Z S₀ : Scheme.{u}} (p : Z ⟶ S) [IsClosedImmersion p] (q : S ⟶ S₀)
    [IsIntegral (Stacks.Blowup.blowUp p.ker)]
    (hX : AlgebraicGeometry.IsRegular (Stacks.Blowup.blowUp p.ker))
    (hXdim : topologicalKrullDim (Stacks.Blowup.blowUp p.ker) ≤ 2)
    [IsIntegral (Stacks.Blowup.exceptionalIdeal p.ker).subscheme]
    (hE : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (show ((Stacks.Blowup.exceptionalIdeal p.ker).subscheme).Modules from
        Scheme.Hom.relativeDifferentials (Stacks.Blowup.exceptionalToCentre p)) 1)
    (r : ℕ)
    [((Scheme.Modules.pullback (Stacks.Blowup.blowUpToBase p.ker)).obj
        (Scheme.Hom.relativeDifferentials q)).IsCoherent]
    [(Scheme.Hom.relativeDifferentials
        (Stacks.Blowup.blowUpToBase p.ker ≫ q)).IsCoherent]
    (U : (Stacks.Blowup.blowUp p.ker).Opens)
    (hU : ∃ x : Stacks.Blowup.blowUp p.ker, x ∈ U)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (((Scheme.Modules.pullback (Stacks.Blowup.blowUpToBase p.ker)).obj
        (Scheme.Hom.relativeDifferentials q)).over U) r]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Hom.relativeDifferentials
        (Stacks.Blowup.blowUpToBase p.ker ≫ q)).over U) r] :
    Nonempty
      (((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨(Stacks.Blowup.blowUp p.ker).sheaf.obj,
              Presheaf.isSheaf_of_isSheaf_comp _ (Stacks.Blowup.blowUp p.ker).sheaf.obj
                (forget₂ CommRingCat RingCat)
                (Stacks.Blowup.blowUp p.ker).ringCatSheaf.property⟩).obj
          (Stacks.Divisors.invertibleSheaf' (Stacks.Blowup.exceptionalIdeal p.ker))).obj
        (reflexiveHull (exteriorPower ((Scheme.Modules.pullback
          (Stacks.Blowup.blowUpToBase p.ker)).obj
            (Scheme.Hom.relativeDifferentials q)) (r : ℤ))) ≅
      reflexiveHull (exteriorPower (Scheme.Hom.relativeDifferentials
        (Stacks.Blowup.blowUpToBase p.ker ≫ q)) (r : ℤ))) ∨
    Nonempty
      (reflexiveHull (exteriorPower ((Scheme.Modules.pullback
          (Stacks.Blowup.blowUpToBase p.ker)).obj
            (Scheme.Hom.relativeDifferentials q)) (r : ℤ)) ≅
      reflexiveHull (exteriorPower (Scheme.Hom.relativeDifferentials
        (Stacks.Blowup.blowUpToBase p.ker ≫ q)) (r : ℤ))) := by
  obtain ⟨k, hk, ⟨e⟩⟩ := exists_eq_zero_or_eq_one_tensorIso_reflexiveHull_exteriorPower
    p q hX hXdim hE r U hU
  rcases hk with rfl | rfl
  · refine Or.inr ⟨Iso.symm ?_ ≪≫ e⟩
    exact Iso.app ((Stacks.SheafOfModules.Tensor.sheafTensor _).mapIso
          (eqToIso (congrArg Stacks.Divisors.invertibleSheaf'
              ((pow_zero (Stacks.Blowup.exceptionalIdeal p.ker)).trans
                Scheme.IdealSheafData.one_eq_top)) ≪≫
            Stacks.Divisors.invertibleSheafTopIsoUnit)) _ ≪≫
        AlgebraicGeometry.SheafOfModules.tensorSheafUnitLeftIso
          (Stacks.Blowup.blowUp p.ker).toRingedSpace _
  · refine Or.inl ⟨Iso.symm ?_ ≪≫ e⟩
    exact Iso.app ((Stacks.SheafOfModules.Tensor.sheafTensor _).mapIso
      (eqToIso (congrArg Stacks.Divisors.invertibleSheaf'
        (pow_one (Stacks.Blowup.exceptionalIdeal p.ker))))) _

end Stacks.BlowupFormsDichotomy

end
