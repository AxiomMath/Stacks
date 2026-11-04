module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassArbitraryRank.BivariantChernCharacter
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassArbitraryRank.ChernCharacterLocallyFree
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassArbitraryRank.SecondAdamsChernScaling
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.PerfectChernCentral
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.LciGysinClass
public import StacksCore.Tactic.StacksAttribute

/-!
# The Gysin map of a local complete intersection morphism commutes with Chern classes

Let `(S, δ)` be as in Situation 02QL, let `f : X ⟶ Y` be a local complete intersection morphism
of schemes locally of finite type over `S` for which the Gysin map exists, and let `ℰ` be a finite
locally free `𝒪_Y`-module, of rank not assumed constant. Stacks 0FF8 records

  `f^! ∘ c_i(ℰ) = c_i(f^*ℰ) ∘ f^!`   and   `f^! ∘ ch(ℰ) = ch(f^*ℰ) ∘ f^!`.

Here `f^! ∈ A^*(X ⟶ Y)^∧` is the Gysin map of Stacks 0FF3, `Stacks.Chow.lciGysinClass`; an
identity in the completed group `A^*(X ⟶ Y)^∧` of Stacks 0FE0 is an identity of all its graded
parts, and the graded parts of `f^! ∘ c_i(ℰ)` are the composites `(f^!)_q ∘ c_i(ℰ)` of the graded
parts `(f^!)_q ∈ A^q(X ⟶ Y)` of `f^!` (Stacks 0FE0). So the two identities are the statements, for
every degree `q`,

  `(f^!)_q ∘ c_i(ℰ) = c_i(f^*ℰ) ∘ (f^!)_q`   in `A^{q+i}(X ⟶ Y)`, and
  `(f^!)_q ∘ ch_p(ℰ) = ch_p(f^*ℰ) ∘ (f^!)_q`   in `A^{q+p}(X ⟶ Y) ⊗ 𝐐`.

## The argument

The source derives both from Stacks 0FF6, the commutation of `res(f^!)` with every bivariant
class. They follow equally from the commutation of the Chern classes and the Chern character with
every bivariant class, which is the route taken here and which needs nothing about `f^!` beyond
its being a bivariant class:

1. the total Chern class `c(ℰ)` of a module of constant rank commutes with every bivariant class
   (Stacks 02UA (2), `Stacks.Chow.TotalChowClass.commutesWith_totalChern`);
2. for `ℰ` of arbitrary rank, `c(ℰ)` and the rank `r(ℰ)` are glued from the rank loci of `ℰ`, a
   decomposition into open and closed subschemes, and commuting glues over such a decomposition;
3. the power sums `P_p(ℰ) = P_p(r(ℰ), c_1(ℰ), c_2(ℰ), …)` are polynomials in these, and the
   total classes commuting with a given class form a subring, so they commute; and
   `ch_p(ℰ) = P_p(ℰ)/p!`;
4. a class commuting with `c ∈ A^q(X' ⟶ X)` on every test scheme gives `c ∘ κ = res(κ) ∘ c`
   (`Stacks.Chow.comp_eq_of_cap_idRule_heq`), and the restrictions are `res(c_i(ℰ)) = c_i(f^*ℰ)`
   and `res(P_p(ℰ)) = P_p(f^*ℰ)` (`Stacks.Chow.res_totalChernClassOfModule`,
   `Stacks.Chow.res_modulePowerSumArbitraryRank`). This last point is the identification
   `res(c_i(ℰ)) = c_i(f^*ℰ)` of the right-hand sides.

## Main results

* `Stacks.Chow.TotalChowClass.commutesWith_totalChernClassOfModule`,
  `Stacks.Chow.TotalChowClass.commutesWith_rankTotalClass`,
  `Stacks.Chow.TotalChowClass.commutesWith_chernPolynomialClass`,
  `Stacks.Chow.TotalChowClass.commutesWith_modulePowerSumArbitraryRank` — the classes `c(ℰ)`,
  `r(ℰ)`, `P(ℰ)` and `P_p(ℰ)` of a module of arbitrary rank commute with every bivariant class.
* `Stacks.Chow.comp_chernClassOfModule` and `Stacks.Chow.comp_chernCharacterOfModule` —
  `c ∘ c_i(ℰ) = c_i(f^*ℰ) ∘ c` and `c ∘ ch_p(ℰ) = ch_p(f^*ℰ) ∘ c` for every bivariant class
  `c ∈ A^q(X ⟶ Y)`.
* `Stacks.Chow.lciGysinClass_comp_chernClassOfModule` and
  `Stacks.Chow.lciGysinClass_comp_chernCharacterOfModule` — **Stacks 0FF8, the Chern class and
  Chern character identities** for the Gysin map `f^!`.

## References

* [Stacks Project, Tag 0FF8](https://stacks.math.columbia.edu/tag/0FF8)
* [Stacks Project, Tag 0FF6](https://stacks.math.columbia.edu/tag/0FF6)
* [Stacks Project, Tag 0FF3](https://stacks.math.columbia.edu/tag/0FF3)
* [Stacks Project, Tag 02UA](https://stacks.math.columbia.edu/tag/02UA)
* [Stacks Project, Tag 0ESW](https://stacks.math.columbia.edu/tag/0ESW)
* [Stacks Project, Tag 0ESX](https://stacks.math.columbia.edu/tag/0ESX)
* [Stacks Project, Tag 0FA7](https://stacks.math.columbia.edu/tag/0FA7)
* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### The Chern classes of a module of arbitrary rank commute with every bivariant class -/

namespace TotalChowClass

variable (C : ChowSituation.{u}) {X X' Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (g : X' ⟶ X) [LocallyOfFiniteType g] {q : ℤ}
  (c : BivariantClass C (gysinSystemOfInvertible C) (g ≫ sX) sX g rfl q)
  (h : Y ⟶ X) [LocallyOfFiniteType h] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (hY : h ≫ sX = sY) (E : Y.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]

/-- **The total Chern class of a module of arbitrary rank commutes with every bivariant class**:
it is glued from the total Chern classes of the constant-rank restrictions to the rank loci, each
of which commutes by Stacks 02UA (2). -/
theorem commutesWith_totalChernClassOfModule :
    (totalChernClassOfModule C sY E).CommutesWith C sX g c h sY hY := by
  refine CommutesWith.of_isClopenDecomposition (c := c) (hY := hY)
    (isClopenDecomposition_rankLociFamily E) fun r ↦ ?_
  have := isFiniteLocallyFreeOfRank_pullback_rankLociFamily E r
  rw [res_totalChernClassOfModule_rankLocus]
  exact commutesWith_totalChern C sX g c _ _ _ _ r.down

/-- **The rank of a module of arbitrary rank commutes with every bivariant class**: on the rank
locus `Y_r` it is `r` times the unit. -/
theorem commutesWith_rankTotalClass :
    (rankTotalClass C sY E).CommutesWith C sX g c h sY hY := by
  refine CommutesWith.of_isClopenDecomposition (c := c) (hY := hY)
    (isClopenDecomposition_rankLociFamily E) fun r ↦ ?_
  rw [rankTotalClass, rankFunctionClass, res_glue]
  exact CommutesWith.zsmul CommutesWith.one _

/-- **Every polynomial `P(ℰ) = P(r(ℰ), c_1(ℰ), c_2(ℰ), …)` of Stacks 0FA7 commutes with every
bivariant class**: the variables do, and the classes commuting with a given class form a
subring. -/
theorem commutesWith_chernPolynomialClass (P : ChernPolynomial) :
    (chernPolynomialClass C sY E P).CommutesWith C sX g c h sY hY := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    rw [show (MvPolynomial.C a : ChernPolynomial) = ((a : ℤ) : ChernPolynomial) by simp,
      map_intCast, ← zsmul_one]
    exact CommutesWith.zsmul CommutesWith.one a
  | add P Q hP hQ =>
    rw [map_add]
    exact CommutesWith.add hP hQ
  | mul_X P o hP =>
    rw [map_mul]
    refine CommutesWith.mul hP ?_
    rcases o with _ | i
    · rw [chernPolynomialClass_X_none]
      exact commutesWith_rankTotalClass C sX g c h sY hY E
    · rw [chernPolynomialClass_X_some]
      exact CommutesWith.homComponent
        (commutesWith_totalChernClassOfModule C sX g c h sY hY E) _

/-- **The power sums `P_p(ℰ)` of a module of arbitrary rank commute with every bivariant
class**: `P_p(ℰ)` is the polynomial `P_p` of Stacks 0F9B evaluated at the rank and the Chern
classes of `ℰ`. -/
theorem commutesWith_modulePowerSumArbitraryRank (p : ℕ) :
    (modulePowerSumArbitraryRank C sY E p).CommutesWith C sX g c h sY hY := by
  rw [modulePowerSumArbitraryRank_eq_chernPolynomialClass]
  exact commutesWith_chernPolynomialClass C sX g c h sY hY E _

end TotalChowClass

/-! ### From commuting on the test schemes to an identity of composites -/

section Composite

variable {C : ChowSituation.{u}} {X X' : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX]
  {sX' : X' ⟶ C.S} [LocallyOfFiniteType sX']

/-- **A total class commuting with every bivariant class gives `c ∘ x_n = res(x)_n ∘ c`.** Let
`x ∈ ∏_{n ≥ 0} A^n(X)` commute, on the test schemes, with every bivariant class along `𝟙 X`. Then
for every `g : X' ⟶ X` and every `c ∈ A^q(X' ⟶ X)`,

  `c ∘ x_n = res(x)_n ∘ c`   in   `A^{q+n}(X' ⟶ X)`,

with `res(x) ∈ ∏_{n ≥ 0} A^n(X')` the restriction of `x` along `g` (Stacks 0B7F). The right side,
a class for `𝟙 X' ≫ g` of degree `n + q`, is read as one for `g ≫ 𝟙 X` of degree `q + n` along the
identity of `X'`, as in Stacks 02UA. -/
theorem comp_eq_res_comp_of_commutesWith (x : TotalChowClass C sX)
    (hx : ∀ {X₁ : Scheme.{u}} (g₁ : X₁ ⟶ X) [LocallyOfFiniteType g₁] {q : ℤ}
      (c : BivariantClass C (gysinSystemOfInvertible C) (g₁ ≫ sX) sX g₁ rfl q),
      x.CommutesWith C sX g₁ c (𝟙 X) sX (Category.id_comp sX))
    (n : ℕ) (g : X' ⟶ X) (hg : g ≫ sX = sX') {q : ℤ} (c : BivariantChowClass C sX' sX g hg q) :
    haveI := BivariantChowClass.locallyOfFiniteType_of_structure sX g hg
    c.comp (BivariantChowClass.equivBivariantClass.symm (x n)) =
      (((BivariantChowClass.equivBivariantClass.symm
          (TotalChowClass.res g hg x n)).comp c).degreeCongr (add_comm (n : ℤ) q)).transport
        (comp_comp_structureMorphism_eq hg (Category.id_comp sX)) (Iso.refl X') (by simp) := by
  have := BivariantChowClass.locallyOfFiniteType_of_structure sX g hg
  refine comp_eq_of_cap_idRule_heq _ _ g hg c fun {T} t _ k α ↦ ?_
  have hβ : pullback.fst g t ≫ sX' = (pullback.fst g t ≫ g) ≫ sX := by
    rw [Category.assoc, hg]
  refine (TotalChowClass.cap_idRule_heq_of_commutesWith x hx n g hg c t k α
    (pullback.fst g t ≫ g) rfl (heq_of_eq pullback.condition.symm)
    (chowGroupCongr C hβ (k - q) (c.cap t k α)) (chowGroupCongr_heq C _ _ _)).trans ?_
  exact (TotalChowClass.op_res_apply g hg x (pullback.fst g t) (k - q) n _ _
    (chowGroupCongr_heq C _ _ _).symm).symm

end Composite

/-! ### Chern classes and the Chern character against an arbitrary bivariant class -/

section Arbitrary

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y) (hf : f ≫ sY = sX) (E : Y.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]

/-- **The Chern character component** `ch_p(ℰ) = P_p(ℰ)/p! ∈ A^p(X) ⊗ 𝐐` of a finite locally free
module of arbitrary rank (Stacks 0ESX). It is the degree-`p` component of
`Stacks.Chow.chernCharacterComponentArbitraryRank`, whose other components vanish
(`Stacks.Chow.isHomogeneous_modulePowerSumArbitraryRank`); see
`Stacks.Chow.chernCharacterOfModule_eq`. -/
def chernCharacterOfModule {Z : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
    (F : Z.Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F] (p : ℕ) :
    TensorProduct ℤ ℚ (chowCohomologyComponent C (gysinSystemOfInvertible C) sZ (p : ℤ)) :=
  ((Nat.factorial p : ℚ)⁻¹) ⊗ₜ[ℤ] modulePowerSumArbitraryRank C sZ F p p

/-- `ch_p(ℰ)` is the degree-`p` component of the Chern character
`Stacks.Chow.chernCharacterComponentArbitraryRank` of `A^*(Y) ⊗ 𝐐 = 𝐐 ⊗ ∏_{n ≥ 0} A^n(Y)`. -/
theorem chernCharacterOfModule_eq (p : ℕ) :
    chernCharacterOfModule C sY E p =
      LinearMap.lTensor ℚ
        (Pi.evalAddMonoidHom
          (fun n : ℕ ↦ chowCohomologyComponent C (gysinSystemOfInvertible C) sY (n : ℤ))
          p).toIntLinearMap
        (chernCharacterComponentArbitraryRank C sY E p) := by
  simp [chernCharacterOfModule, chernCharacterComponentArbitraryRank]
  rfl

include hf in
/-- **`c ∘ c_i(ℰ) = c_i(f^*ℰ) ∘ c`** for every bivariant class `c ∈ A^q(X ⟶ Y)` and every finite
locally free `𝒪_Y`-module `ℰ` of arbitrary rank, with `c_i` the Chern classes of Stacks 0ESW. -/
theorem comp_chernClassOfModule (i : ℕ) {q : ℤ} (c : BivariantChowClass C sX sY f hf q) :
    haveI := BivariantChowClass.locallyOfFiniteType_of_structure sY f hf
    haveI := isFiniteLocallyFree_pullback_of_isFiniteLocallyFree f E
    c.comp (BivariantChowClass.equivBivariantClass.symm (chernClassOfModule C sY E i)) =
      (((BivariantChowClass.equivBivariantClass.symm
          (chernClassOfModule C sX ((Scheme.Modules.pullback f).obj E) i)).comp c).degreeCongr
        (add_comm (i : ℤ) q)).transport (comp_comp_structureMorphism_eq hf (Category.id_comp sY))
        (Iso.refl X) (by simp) := by
  have := BivariantChowClass.locallyOfFiniteType_of_structure sY f hf
  have := isFiniteLocallyFree_pullback_of_isFiniteLocallyFree f E
  have H := comp_eq_res_comp_of_commutesWith (totalChernClassOfModule C sY E)
    (fun g₁ _ _ c₁ ↦ TotalChowClass.commutesWith_totalChernClassOfModule C sY g₁ c₁ (𝟙 Y) sY
      (Category.id_comp sY) E) i f hf c
  rw [res_totalChernClassOfModule C sY f hf E, totalChernClassOfModule_apply,
    totalChernClassOfModule_apply] at H
  exact H

include hf in
/-- **`c ∘ ch_p(ℰ) = ch_p(f^*ℰ) ∘ c`** in `A^{q+p}(X ⟶ Y) ⊗ 𝐐`, for every bivariant class
`c ∈ A^q(X ⟶ Y)` and every finite locally free `𝒪_Y`-module `ℰ` of arbitrary rank, the composites
with a rational class being the rational extensions of the composites of Stacks 0B75. -/
theorem comp_chernCharacterOfModule (p : ℕ) {q : ℤ} (c : BivariantChowClass C sX sY f hf q) :
    haveI := BivariantChowClass.locallyOfFiniteType_of_structure sY f hf
    haveI := isFiniteLocallyFree_pullback_of_isFiniteLocallyFree f E
    LinearMap.lTensor ℚ (c.compRightHom f hf (p : ℤ)).toIntLinearMap
        (chernCharacterOfModule C sY E p) =
      LinearMap.lTensor ℚ (c.compLeftHom f hf (p : ℤ)).toIntLinearMap
        (chernCharacterOfModule C sX ((Scheme.Modules.pullback f).obj E) p) := by
  have := BivariantChowClass.locallyOfFiniteType_of_structure sY f hf
  have := isFiniteLocallyFree_pullback_of_isFiniteLocallyFree f E
  simp only [chernCharacterOfModule, LinearMap.lTensor_tmul]
  congr 1
  have H := comp_eq_res_comp_of_commutesWith (modulePowerSumArbitraryRank C sY E p)
    (fun g₁ _ _ c₁ ↦ TotalChowClass.commutesWith_modulePowerSumArbitraryRank C sY g₁ c₁ (𝟙 Y)
      sY (Category.id_comp sY) E p) p f hf c
  rw [res_modulePowerSumArbitraryRank C sY f hf E] at H
  exact H

end Arbitrary

/-! ### Stacks 0FF8 for the Gysin map -/

section Gysin

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y) [LocallyOfFiniteType f] (hfs : f ≫ sY = sX)
  (hf : IsLocalCompleteIntersectionMorphism f) (F : SmoothFactorization f)

/-- The graded part `(f^!)_q ∈ A^q(X ⟶ Y)` of the Gysin map `f^! ∈ A^*(X ⟶ Y)^∧` of Stacks 0FF3
(Stacks 0FE0), as a bivariant class of Stacks 0B76. -/
def lciGysinClassComponent (q : ℤ) : BivariantChowClass C sX sY f hfs q :=
  letI := LocallyOfFiniteType.isLocallyNoetherian sX
  letI := LocallyOfFiniteType.isLocallyNoetherian sY
  BivariantChowClass.equivBivariantClass.symm
    (completedBivariantSequenceOfInvertible C sX sY f hfs (lciGysinClass C sX sY f hfs hf F) q)

/-- **Stacks 0FF8, the Chern classes.** Let `f : X ⟶ Y` be a local complete intersection morphism
of schemes locally of finite type over `S` for which the Gysin map exists, with `f^!` the Gysin
map of Stacks 0FF3 built from a factorization `F` of `f`, and let `ℰ` be a finite locally free
`𝒪_Y`-module of arbitrary rank. Then

  `f^! ∘ c_i(ℰ) = c_i(f^*ℰ) ∘ f^!`,

stated, as an identity in the completed group `A^*(X ⟶ Y)^∧` of Stacks 0FE0 is, degree by degree:
for every `q`, `(f^!)_q ∘ c_i(ℰ) = c_i(f^*ℰ) ∘ (f^!)_q` in `A^{q+i}(X ⟶ Y)`. The Chern classes are
those of Stacks 0ESW. -/
@[stacks 0FF8 "first assertion: f^! ∘ c_i(E) = c_i(f^*E) ∘ f^! for the Gysin map f^! of 0FF3 \
(`lciGysinClass`) and E finite locally free of any rank (c_i of 0ESW), stated in every graded \
part (f^!)_q of f^! in A^*(X → Y)^∧; the right side is c_i(f^*E) itself, not res(c_i(E))"]
theorem lciGysinClass_comp_chernClassOfModule (E : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] (i : ℕ) (q : ℤ) :
    haveI := isFiniteLocallyFree_pullback_of_isFiniteLocallyFree f E
    (lciGysinClassComponent C sX sY f hfs hf F q).comp
        (BivariantChowClass.equivBivariantClass.symm (chernClassOfModule C sY E i)) =
      (((BivariantChowClass.equivBivariantClass.symm
          (chernClassOfModule C sX ((Scheme.Modules.pullback f).obj E) i)).comp
            (lciGysinClassComponent C sX sY f hfs hf F q)).degreeCongr
        (add_comm (i : ℤ) q)).transport (comp_comp_structureMorphism_eq hfs (Category.id_comp sY))
        (Iso.refl X) (by simp) :=
  comp_chernClassOfModule C sX sY f hfs E i _

/-- **Stacks 0FF8, the Chern character.** In the situation of
`Stacks.Chow.lciGysinClass_comp_chernClassOfModule`,

  `f^! ∘ ch(ℰ) = ch(f^*ℰ) ∘ f^!`,

stated degree by degree: for every `q` and every `p`, `(f^!)_q ∘ ch_p(ℰ) = ch_p(f^*ℰ) ∘ (f^!)_q` in
`A^{q+p}(X ⟶ Y) ⊗ 𝐐`, with `ch_p(ℰ) = P_p(ℰ)/p!` the Chern character of Stacks 0ESX
(`Stacks.Chow.chernCharacterOfModule`) and the composites with a rational class the rational
extensions of those of Stacks 0B75. -/
@[stacks 0FF8 "first assertion, for the Chern character: f^! ∘ ch(E) = ch(f^*E) ∘ f^! in \
A^*(X → Y) ⊗ Q, stated for every graded part (f^!)_q of the Gysin map of 0FF3 and every \
component ch_p(E) = P_p(E)/p! of the Chern character of 0ESX, E finite locally free of any rank"]
theorem lciGysinClass_comp_chernCharacterOfModule (E : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] (p : ℕ) (q : ℤ) :
    haveI := isFiniteLocallyFree_pullback_of_isFiniteLocallyFree f E
    LinearMap.lTensor ℚ ((lciGysinClassComponent C sX sY f hfs hf F q).compRightHom f hfs
        (p : ℤ)).toIntLinearMap (chernCharacterOfModule C sY E p) =
      LinearMap.lTensor ℚ ((lciGysinClassComponent C sX sY f hfs hf F q).compLeftHom f hfs
        (p : ℤ)).toIntLinearMap
        (chernCharacterOfModule C sX ((Scheme.Modules.pullback f).obj E) p) :=
  comp_chernCharacterOfModule C sX sY f hfs E p _

end Gysin

end Stacks.Chow

end
