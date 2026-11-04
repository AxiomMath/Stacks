module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeFieldPoint
public import StacksFrontier.AlgebraicGeometry.Variety.Bertini.VanishingDivisorSmoothOnX

/-!
# The two points lie on the smooth divisor the Bertini step produces

`Stacks.SectionsVanishingOnSubscheme.exists_ne_zero_smooth_divisorOnX_pair` produces, for the
Bertini step of [Stacks, Tag 0FH7], a nonzero `v ∈ V_n` whose divisor `H_v` is smooth over `k` on
the whole of `X`, with germs at the two closed points `x` and `x'` outside `𝔪ₓ²ℒₓ` and
`𝔪ₓ'²ℒₓ'`. The next step of the source reduces the class `[x] - [x']` to `H_v`, and for that it
needs the two points to lie on `H_v` *as morphisms*: a `k`-rational point `ξ : Spec k ⟶ X` has to
factor as `ξ_H ≫ ι` through the closed immersion `ι : H_v ⟶ X`.

Two things are needed and neither is in the statement above. The first is the reverse inclusion
`{x, x'} ⊆ Z`, which is what makes every member of `V_n` vanish at the two points: the preceding
statement deliberately assumes only `Z ⊆ {x, x'}`, which is what its smoothness conclusion uses,
and says so. It is added here as a second, independent hypothesis, so that no existing statement
is weakened. The second is the passage from the *topological* membership `x ∈ Z` to a
factorization of a morphism, which is
`AlgebraicGeometry.exists_lift_zeroScheme_of_mem_support_of_pullbackGlobalSections_eq_zero`.

## Main results

* `Stacks.SectionsVanishingOnSubscheme.exists_ne_zero_smooth_divisorOnX_pair_exists_lift`: **the
  Bertini step of [Stacks, Tag 0FH7] with the two factorizations** — for `Z = {x, x'}` there is a
  nonzero `v ∈ V_n` whose divisor on `X` is smooth over `k`, whose germs at `x` and `x'` avoid
  `𝔪ₓ²ℒₓ` and `𝔪ₓ'²ℒₓ'`, and through whose divisor every point with values in a field over `x`,
  and every one over `x'`, factors.
* `Stacks.SectionsVanishingOnSubscheme.exists_ne_zero_smooth_divisorOnX_pair_rationalPoints`: the
  same with the two points taken to be the `k`-rational points of `X` that the two closed points
  determine, which is the form the descent of the class asks for: the four conclusions
  `ξ_H ≫ ι = ξ`, `ξ'_H ≫ ι = ξ'` and the two section properties of `ξ_H` and `ξ'_H` are exactly
  the hypotheses `hfac`, `hfac'`, `hxH` and `hxH'` of
  `Stacks.WeilCohomology.rationalPointChowClass_sub_eq_zsmul_chowPushforward` at `ι` the closed
  immersion of `H_v`, `p := f` and `pH := ι ≫ f`.

## Implementation notes

A `k`-rational point of `X` at a closed point is `AlgebraicGeometry.pointOfClosedPoint`, which
needs `k` algebraically closed and `X` locally of finite type over `k` — both already hypotheses
of the Bertini step, the second through `Smooth f`. Its two properties used here are that it is a
section of `f` (`AlgebraicGeometry.pointOfClosedPoint_comp`) and that its image is the chosen
closed point (`AlgebraicGeometry.pointOfClosedPoint_apply`).

The first statement is not about rational points at all: its two morphisms are arbitrary points
with values in a field whose image is `x` and `x'`, because the factorization criterion sees only
the image point. The second is that statement at the canonical `k`-rational points.

That a member of `V_n` vanishes at `x` is read off its membership of `V_n`
(`Stacks.SectionsVanishingOnSubscheme.mem_vanishingSections_iff`: it restricts to zero on `V(I)`)
together with `x ∈ Z`; no germ computation is involved, and in particular the germ conditions of
the Bertini step play no part here.

No `@[stacks]` attribute is attached. [Stacks, Tag 0FH7] asserts a divisibility of zero-cycle
classes after a finite separable extension; what is proved here is the output of its Bertini
reduction together with the containment of the two points, and the tag's remaining steps — the
induction on `dim X`, the curve case and the Jacobian of [Stacks, Tag 0BA0] — are not available.

## References

* [Stacks Project, Tag 02OR](https://stacks.math.columbia.edu/tag/02OR)
* [Stacks Project, Tag 0356](https://stacks.math.columbia.edu/tag/0356)
* [Stacks Project, Tag 0FD5](https://stacks.math.columbia.edu/tag/0FD5)
* [Stacks Project, Tag 0FH7](https://stacks.math.columbia.edu/tag/0FH7)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open Stacks.Ample Stacks.ProjectiveFromSections
open Stacks.ImmersionEvaluationSurjective

universe u

namespace Stacks.SectionsVanishingOnSubscheme

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (I : X.IdealSheafData) {L : X.Modules} [IsInvertibleModule X L] (n : ℤ)
  [FiniteDimensional k (Stacks.Bertini.globalSections k f (tensorPowModule X L n))]
  [FiniteDimensional k (vanishingSections k f I L n)]

omit [FiniteDimensional k (vanishingSections k f I L n)] in
/-- **A point with values in a field at a point of `Z` factors through the divisor of any member
of `V_n`.** Every member of `V_n` restricts to zero on `V(I)`, so `V(I)` lies inside its divisor;
a point with values in a field whose image lies in `Z = |V(I)|` therefore factors through that
divisor.

This is
`AlgebraicGeometry.exists_lift_zeroScheme_of_mem_support_of_pullbackGlobalSections_eq_zero` at
the section of the member, the vanishing hypothesis being its membership of `V_n`. -/
theorem exists_lift_divisorOnX_subschemeι_of_mem_support {K : Type u} [Field K]
    (w : vanishingSections k f I L n) (g : Spec (.of K) ⟶ X)
    (hg : g (IsLocalRing.closedPoint K) ∈ I.support) :
    ∃ gH : Spec (.of K) ⟶ ((familyDivisorsOnX k f I (L := L) n).divisor w).subscheme,
      gH ≫ ((familyDivisorsOnX k f I (L := L) n).divisor w).subschemeι = g := by
  have hinv : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (tensorPowModule X L n) := (familyDivisorsOnX k f I (L := L) n).isInvertible
  exact AlgebraicGeometry.exists_lift_zeroScheme_of_mem_support_of_pullbackGlobalSections_eq_zero
    X (tensorPowModule X L n) ((familyDivisorsOnX k f I (L := L) n).sectionOf w) I
    ((mem_vanishingSections_iff k f I L n w).mp w.2) g hg

/-- **The Bertini step of [Stacks, Tag 0FH7], with the two points on the divisor.** The
hypotheses are those of
`Stacks.SectionsVanishingOnSubscheme.exists_ne_zero_smooth_divisorOnX_pair` together with the
reverse inclusion `{x, x'} ⊆ Z`, and two points `ξ`, `ξ'` with values in a field whose images are
`x` and `x'`. The conclusion is that one of the nonzero members `v ∈ V_n` with `H_v` smooth over
`k` and germs at `x` and `x'` outside `𝔪ₓ²ℒₓ` and `𝔪ₓ'²ℒₓ'` has, in addition, both `ξ` and `ξ'`
factoring through `H_v`.

The smoothness and the germ conditions are
`Stacks.SectionsVanishingOnSubscheme.exists_ne_zero_smooth_divisorOnX_pair`; the two
factorizations are
`Stacks.SectionsVanishingOnSubscheme.exists_lift_divisorOnX_subschemeι_of_mem_support`, which is
where the new hypothesis `{x, x'} ⊆ Z` is spent and the only place it is used. -/
theorem exists_ne_zero_smooth_divisorOnX_pair_exists_lift [IsAlgClosed k] [Smooth f]
    [Module.Finite k (subschemeSections k f I (L := L) n)]
    (hsm : Smooth ((openComplement I).ι ≫ f))
    {N : ℕ} (b : Module.Basis (Fin (N + 1)) k (vanishingSections k f I L n))
    (hgen : GeneratesOffSupport k f I L n)
    (himm : IsImmersion (toProjectiveSpaceOfVanishingSections k f b hgen))
    {p : ℕ} {b' : Module.Basis (Fin (p + 1)) k
      (Stacks.Bertini.globalSections k f (tensorPowModule X L n))}
    {hb' : (ambientFamilyDivisors k f (L := L) n).GeneratesBy b'}
    (himm' : (ambientFamilyDivisors k f (L := L) n).IsImmersive b' hb')
    {x x' : X} (hx : IsClosed ({x} : Set X)) (hx' : IsClosed ({x'} : Set X))
    {m : ℕ} (hdim : topologicalKrullDimAt X x = (m : WithBot ℕ∞))
    (hdim' : topologicalKrullDimAt X x' = (m : WithBot ℕ∞))
    (hcond : Module.finrank k (subschemeSections k f I (L := L) n) ≤ m)
    (hsupport : (I.support : Set X) ⊆ {x, x'})
    (hmem : ({x, x'} : Set X) ⊆ (I.support : Set X))
    {K : Type u} [Field K] (ξ ξ' : Spec (.of K) ⟶ X)
    (hξ : ξ (IsLocalRing.closedPoint K) = x) (hξ' : ξ' (IsLocalRing.closedPoint K) = x') :
    ∃ w : vanishingSections k f I L n, w ≠ 0 ∧
      Smooth (((familyDivisorsOnX k f I (L := L) n).divisor w).subschemeι ≫ f) ∧
      ((tensorPowModule X L n).presheaf.Γgerm x).hom
          ((familyDivisorsOnX k f I (L := L) n).sectionOf w) ∉
        maximalSqSmul (tensorPowModule X L n) x ∧
      ((tensorPowModule X L n).presheaf.Γgerm x').hom
          ((familyDivisorsOnX k f I (L := L) n).sectionOf w) ∉
        maximalSqSmul (tensorPowModule X L n) x' ∧
      (∃ ξH : Spec (.of K) ⟶ ((familyDivisorsOnX k f I (L := L) n).divisor w).subscheme,
        ξH ≫ ((familyDivisorsOnX k f I (L := L) n).divisor w).subschemeι = ξ) ∧
      (∃ ξH' : Spec (.of K) ⟶ ((familyDivisorsOnX k f I (L := L) n).divisor w).subscheme,
        ξH' ≫ ((familyDivisorsOnX k f I (L := L) n).divisor w).subschemeι = ξ') := by
  obtain ⟨w, hw0, hwsm, hwx, hwx'⟩ :=
    exists_ne_zero_smooth_divisorOnX_pair k f I n hsm b hgen himm himm' hx hx' hdim hdim' hcond
      hsupport
  refine ⟨w, hw0, hwsm, hwx, hwx',
    exists_lift_divisorOnX_subschemeι_of_mem_support k f I n w ξ ?_,
    exists_lift_divisorOnX_subschemeι_of_mem_support k f I n w ξ' ?_⟩
  · exact hξ ▸ hmem (Set.mem_insert x {x'})
  · exact hξ' ▸ hmem (Set.mem_insert_of_mem x rfl)

/-- **The Bertini step of [Stacks, Tag 0FH7] with the two `k`-rational points on the divisor.**
Over an algebraically closed field a closed point `x` of a scheme locally of finite type carries
a `k`-rational point `ξ_x = AlgebraicGeometry.pointOfClosedPoint f x hx` of `X`, and this is the
previous statement at `ξ_x` and `ξ_{x'}`, with the two section properties of the lifted points
added.

The last four conclusions are exactly the hypotheses `hfac`, `hfac'`, `hxH` and `hxH'` of
`Stacks.WeilCohomology.rationalPointChowClass_sub_eq_zsmul_chowPushforward`, whose remaining data
is the closed immersion `ι` of `H_v` into `X`, the structure morphisms `p := f` and `pH := ι ≫ f`
and the equation `hι : ι ≫ p = pH`, which is a reflexivity. So the divisibility of
`[ξ_x] - [ξ_{x'}]` proved on `H_v` transports to `X`. -/
theorem exists_ne_zero_smooth_divisorOnX_pair_rationalPoints [IsAlgClosed k] [Smooth f]
    [Module.Finite k (subschemeSections k f I (L := L) n)]
    (hsm : Smooth ((openComplement I).ι ≫ f))
    {N : ℕ} (b : Module.Basis (Fin (N + 1)) k (vanishingSections k f I L n))
    (hgen : GeneratesOffSupport k f I L n)
    (himm : IsImmersion (toProjectiveSpaceOfVanishingSections k f b hgen))
    {p : ℕ} {b' : Module.Basis (Fin (p + 1)) k
      (Stacks.Bertini.globalSections k f (tensorPowModule X L n))}
    {hb' : (ambientFamilyDivisors k f (L := L) n).GeneratesBy b'}
    (himm' : (ambientFamilyDivisors k f (L := L) n).IsImmersive b' hb')
    {x x' : X} (hx : IsClosed ({x} : Set X)) (hx' : IsClosed ({x'} : Set X))
    {m : ℕ} (hdim : topologicalKrullDimAt X x = (m : WithBot ℕ∞))
    (hdim' : topologicalKrullDimAt X x' = (m : WithBot ℕ∞))
    (hcond : Module.finrank k (subschemeSections k f I (L := L) n) ≤ m)
    (hsupport : (I.support : Set X) ⊆ {x, x'})
    (hmem : ({x, x'} : Set X) ⊆ (I.support : Set X)) :
    ∃ w : vanishingSections k f I L n, w ≠ 0 ∧
      Smooth (((familyDivisorsOnX k f I (L := L) n).divisor w).subschemeι ≫ f) ∧
      ((tensorPowModule X L n).presheaf.Γgerm x).hom
          ((familyDivisorsOnX k f I (L := L) n).sectionOf w) ∉
        maximalSqSmul (tensorPowModule X L n) x ∧
      ((tensorPowModule X L n).presheaf.Γgerm x').hom
          ((familyDivisorsOnX k f I (L := L) n).sectionOf w) ∉
        maximalSqSmul (tensorPowModule X L n) x' ∧
      ∃ ξH ξH' : Spec (.of k) ⟶ ((familyDivisorsOnX k f I (L := L) n).divisor w).subscheme,
        ξH ≫ ((familyDivisorsOnX k f I (L := L) n).divisor w).subschemeι =
            AlgebraicGeometry.pointOfClosedPoint f x hx ∧
          ξH' ≫ ((familyDivisorsOnX k f I (L := L) n).divisor w).subschemeι =
            AlgebraicGeometry.pointOfClosedPoint f x' hx' ∧
          ξH ≫ ((familyDivisorsOnX k f I (L := L) n).divisor w).subschemeι ≫ f =
            𝟙 (Spec (.of k)) ∧
          ξH' ≫ ((familyDivisorsOnX k f I (L := L) n).divisor w).subschemeι ≫ f =
            𝟙 (Spec (.of k)) := by
  obtain ⟨w, hw0, hwsm, hwx, hwx', ⟨ξH, hξH⟩, ⟨ξH', hξH'⟩⟩ :=
    exists_ne_zero_smooth_divisorOnX_pair_exists_lift k f I n hsm b hgen himm himm' hx hx'
      hdim hdim' hcond hsupport hmem (AlgebraicGeometry.pointOfClosedPoint f x hx)
      (AlgebraicGeometry.pointOfClosedPoint f x' hx')
      (AlgebraicGeometry.pointOfClosedPoint_apply f x hx _)
      (AlgebraicGeometry.pointOfClosedPoint_apply f x' hx' _)
  refine ⟨w, hw0, hwsm, hwx, hwx', ξH, ξH', hξH, hξH', ?_, ?_⟩
  · rw [← Category.assoc, hξH]
    exact AlgebraicGeometry.pointOfClosedPoint_comp f x hx
  · rw [← Category.assoc, hξH']
    exact AlgebraicGeometry.pointOfClosedPoint_comp f x' hx'

end Stacks.SectionsVanishingOnSubscheme

end
