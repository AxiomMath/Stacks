module

public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeIdealSheaf
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeRegular
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.FirstChernClassSetup
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.WeakChernClasses.CohomologicalChernCharacter

/-!
# The cohomological Chern character of a Weil cohomology theory

Tag 0FIE of the Stacks Project: given data (D0), (D1), (D2') satisfying axioms (A1), (A2), (A3)
and (A4), there is a unique rule which assigns to every smooth projective `X` over `k` a ring
homomorphism

`ch^H : K₀(Vect(X)) ⟶ ∏_{i ≥ 0} H^{2i}(X)(i)`

compatible with pullbacks such that `ch^H(ℒ) = exp(c₁^H(ℒ))` for every invertible
`𝒪_X`-module `ℒ`.

## The proof

The source's proof applies Proposition 45.12.4 (Tag 0FI9) to the category of smooth projective
schemes over `k`, the functor `A : X ↦ ⨁_{i ≥ 0} H^{2i}(X)(i)` and `c₁^H`. This file checks the
standing assumptions of Section 45.12 for these data:

* the category has the closure properties (1), (2), (3)(a)–(c):
  `Stacks.WeilCohomology.SmoothProjectiveScheme`;
* condition (2) is axiom (A1), condition (3) is axiom (A2), condition (5) is axiom (A4) applied to
  the divisor `𝐏(𝓕) ⊂ 𝐏(ℰ)`, and condition (4) comes from axiom (A3):
  `Stacks.WeilCohomology.FirstChernClassData.toChernSetup` and the theorems below.

**A gap in the source's proof.** Condition (4) asks the projective bundle formula to be
*bijective* on `A`. In this chapter graded commutative algebras are graded by `𝐙`, and nothing in
(D0)–(D2') or (A1)–(A4) makes `H^*` vanish in negative degrees. When it does not, (A3) gives
injectivity of the formula on `A` but not surjectivity: for `t ∈ H^{-2}(X)(-1)` the class
`c₁^H(𝒪_P(1)) ∪ p^*t` lies in `A^0(P)` but not in the image of `A(X)^{r+1}`. An example satisfying
every one of (D0)–(D2') and (A1)–(A4) is `H^* ⊗_F F[t, t⁻¹]` with `t` of degree `-2`, for any
cohomology theory `H^*` satisfying them. So Tag 0FI9 does not apply verbatim. What the
construction of Chern classes and of the Chern character uses of condition (4) is injectivity and
the resolution of `c₁^A(𝒪_P(1))^{r+1}`, whose coefficients sit in the positive degrees
`2(r + 1 - i)`; both follow from (A3). The proof therefore runs through the standing situation in
that weak form, `Stacks.WeilCohomology.Weak.ChernSetup`, and the statement is the source's.

## Main results

* `Stacks.WeilCohomology.FirstChernClassData.existsUnique_cohomologicalChernCharacter`:
  **Tag 0FIE.**

## References

* [Stacks Project, Tag 0FIE](https://stacks.math.columbia.edu/tag/0FIE)
* [Stacks Project, Tag 0FI4](https://stacks.math.columbia.edu/tag/0FI4)
* [Stacks Project, Tag 0FI9](https://stacks.math.columbia.edu/tag/0FI9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct Opposite

universe u w

namespace Stacks.WeilCohomology

open SmoothProjectiveScheme

namespace FirstChernClassData

variable {k : Type u} [Field k] {F : Type w} [Field F] (𝔇 : FirstChernClassData k F)

/-! ### Condition (3) -/

/-- **Condition (3) of Section 45.12** for `A`, from axiom (A2). -/
theorem pullbackFirstChernCondition (hA1 : 𝔇.CoproductAxiom) (hA3 : 𝔇.ProjectiveBundleAxiom)
    (hA2 : 𝔇.PullbackAxiom) :
    Weak.PullbackFirstChernCondition (𝔇.toChernSetup hA1 hA3) := fun f L hL =>
  Subtype.ext ((𝔇.κ_pullTw f 1 _).symm.trans (congrArg (𝔇.κ _ 1) (hA2 f L hL)))

/-! ### Clause (3)(b) -/

/-- The identifications of the bundles of clause-(3)(a) objects with `𝐏(ℰ)` commute with every
morphism of the underlying schemes. -/
private theorem comp_bundleObject_iso_hom {X X' : (SmoothProjectiveScheme k).FullSubcategory}
    {E : ((toScheme k).obj X).Modules} {E' : ((toScheme k).obj X').Modules} {r r' : ℕ}
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank E (r + 1)]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank E' (r' + 1)]
    (g : (bundleObject X' E' r').bundle.obj.left ⟶ (bundleObject X E r).bundle.obj.left) :
    g ≫ (bundleObject X E r).iso.hom = (bundleObject X' E' r').iso.hom ≫ g := by
  rw [bundleObject_iso, bundleObject_iso, Iso.refl_hom, Iso.refl_hom]
  exact (Category.comp_id g).trans (Category.id_comp g).symm

/-- **Clause (3)(b) of Section 45.12**: the base change morphism `𝐏(f^*ℰ) ⟶ 𝐏(ℰ)` is a morphism
of smooth projective schemes over `k`. -/
theorem bundleCompareClause (hA1 : 𝔇.CoproductAxiom) (hA3 : 𝔇.ProjectiveBundleAxiom) :
    Weak.BundleCompareClause (𝔇.toChernSetup hA1 hA3) := by
  intro X X' f E r hE hE'
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E (r + 1)
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
    ((Scheme.Modules.pullback ((toScheme k).map f)).obj E) (r + 1)
  let g₀ := Stacks.Chow.bundleBaseChangeHom ((toScheme k).map f) E
    ((Scheme.Modules.pullback ((toScheme k).map f)).obj E) (Iso.refl _).symm
  have hg₀ : g₀ ≫ Stacks.Chow.bundleProj E =
      Stacks.Chow.bundleProj ((Scheme.Modules.pullback ((toScheme k).map f)).obj E) ≫
        (toScheme k).map f :=
    Stacks.Chow.bundleBaseChangeHom_bundleProj _ _ _ _
  refine ⟨@homMk k _ (@bundle k _ X' _ r hE') (@bundle k _ X E r hE) g₀ ?_, ?_, ?_⟩
  · show g₀ ≫ Stacks.Chow.bundleProj E ≫ X.obj.hom =
      Stacks.Chow.bundleProj ((Scheme.Modules.pullback ((toScheme k).map f)).obj E) ≫ X'.obj.hom
    rw [reassoc_of% hg₀]
    exact congrArg (fun φ => Stacks.Chow.bundleProj
      ((Scheme.Modules.pullback ((toScheme k).map f)).obj E) ≫ φ) (w f)
  · exact hom_ext' hg₀
  · show g₀ ≫ (@bundleObject k _ X E r hE).iso.hom =
      (@bundleObject k _ X' _ r hE').iso.hom ≫ g₀
    exact comp_bundleObject_iso_hom g₀

/-! ### Clause (3)(c) and condition (5) -/

/-- The invertible module of the zero scheme of a regular section is the module itself. -/
theorem picardClassOf_divisorSheaf_zeroScheme {Y : Scheme.{u}} (L : Y.Modules)
    [hL : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L]
    (s : L.sections)
    [hD : Stacks.Divisors.IsEffectiveCartierDivisor
      (AlgebraicGeometry.zeroScheme Y L (s.eval (op ⊤)))] :
    picardClassOf Y
        (Stacks.Divisors.divisorSheaf (AlgebraicGeometry.zeroScheme Y L (s.eval (op ⊤))))
        (Stacks.Divisors.isInvertible_divisorSheaf _) = picardClassOf Y L hL := by
  have hreg := (AlgebraicGeometry.isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection
    Y L s).mp hD
  exact picardClassOf_eq_of_iso _ _ _ _ _
    (invertibleSheafIsoZeroSchemeOfIsRegularSection L s hreg).symm

/-- **Clause (3)(c) of Section 45.12 together with condition (5)** for `A`: the closed immersion
`𝐏(𝓕) ⟶ 𝐏(ℰ)` is a morphism of smooth projective schemes over `k`, exhibiting `𝐏(𝓕)` as an
effective Cartier divisor, and condition (5) is axiom (A4) for that divisor. -/
theorem divisorDatumClause (hA1 : 𝔇.CoproductAxiom) (hA3 : 𝔇.ProjectiveBundleAxiom)
    (hA4 : 𝔇.DivisorAxiom) :
    Weak.DivisorDatumClause (𝔇.toChernSetup hA1 hA3) := by
  intro X T hT _ r hF hE
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree T.X₂
    (r + 1 + 1)
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree T.X₃
    (r + 1)
  have := hT.epi_g
  let i₀ := Stacks.Chow.GenuineChern.bundleEmbedding T.g
  have hi₀ : i₀ ≫ Stacks.Chow.bundleProj T.X₂ = Stacks.Chow.bundleProj T.X₃ :=
    Stacks.Chow.GenuineChern.bundleEmbedding_comp_bundleProj _
  let i : @bundle k _ X T.X₃ r hF ⟶ @bundle k _ X T.X₂ (r + 1) hE :=
    @homMk k _ (@bundle k _ X T.X₃ r hF) (@bundle k _ X T.X₂ (r + 1) hE) i₀ (by
      show i₀ ≫ Stacks.Chow.bundleProj T.X₂ ≫ X.obj.hom = Stacks.Chow.bundleProj T.X₃ ≫ X.obj.hom
      rw [reassoc_of% hi₀])
  refine ⟨i, ⟨hom_ext' hi₀, ?_⟩, ?_⟩
  · show i₀ ≫ (@bundleObject k _ X T.X₂ (r + 1) hE).iso.hom =
      (@bundleObject k _ X T.X₃ r hF).iso.hom ≫ i₀
    exact comp_bundleObject_iso_hom i₀
  · intro L hLinv hdiv a ha
    obtain ⟨s, hD, e, he⟩ := hdiv
    let D := @Stacks.Divisors.zeroScheme _ L hLinv (s.eval (op ⊤))
    have hD' : Stacks.Divisors.IsEffectiveCartierDivisor D := hD.1
    have hpic : picardClassOf (Stacks.Chow.bundle T.X₂) (Stacks.Divisors.divisorSheaf D)
        (Stacks.Divisors.isInvertible_divisorSheaf D) = picardClassOf _ L hLinv :=
      @picardClassOf_divisorSheaf_zeroScheme (Stacks.Chow.bundle T.X₂) L hLinv s hD'
    let a' : 𝔇.A (@bundle k _ X T.X₂ (r + 1) hE) := a
    -- axiom (A4) for the divisor `𝐏(𝓕) ⊂ 𝐏(ℰ)`
    have hA := hA4 (@bundle k _ X T.X₂ (r + 1) hE) (@bundle k _ X T.X₃ r hF) i D hD' e.symm
      (by
        show e.inv ≫ D.subschemeι = i₀
        rw [← he, Iso.inv_hom_id_assoc])
      (a' : 𝔇.H (@bundle k _ X T.X₂ (r + 1) hE))
      (congrArg Subtype.val (show 𝔇.pullA i a' = 0 from ha))
    have hcls : picardClassOf ((toScheme k).obj (@bundle k _ X T.X₂ (r + 1) hE))
        ((Scheme.Modules.pullback (@bundleObject k _ X T.X₂ (r + 1) hE).iso.hom).obj L)
        (isInvertible_pullback_obj _ L hLinv) =
          picardClassOf ((toScheme k).obj (@bundle k _ X T.X₂ (r + 1) hE))
            (Stacks.Divisors.divisorSheaf D) (Stacks.Divisors.isInvertible_divisorSheaf D) :=
      (picardClassOf_eq_of_iso _ _ _ _ _
        ((Scheme.Modules.pullbackCongr (show (@bundleObject k _ X T.X₂ (r + 1) hE).iso.hom = 𝟙 _ by
          rw [bundleObject_iso, Iso.refl_hom])).app _ ≪≫
          (Scheme.Modules.pullbackId _).app _)).trans hpic.symm
    refine Subtype.ext ?_
    refine (congrArg (fun P => (a' : 𝔇.H (@bundle k _ X T.X₂ (r + 1) hE)) *
        𝔇.κ (@bundle k _ X T.X₂ (r + 1) hE) 1 (𝔇.c₁ (@bundle k _ X T.X₂ (r + 1) hE) P) : _ → _)
      hcls).trans ?_
    have h0 := congrArg (𝔇.κ (@bundle k _ X T.X₂ (r + 1) hE) 1) hA
    rw [κ, tateTwistCoordinates_tateCupLeft, map_zero] at h0
    exact h0

/-! ### The `𝐐`-structure -/

variable [CharZero F]

/-- `A(X)` is a `𝐐`-algebra through `𝐐 ⊆ F`. -/
instance algebraRatA (X : (SmoothProjectiveScheme k).FullSubcategory) : Algebra ℚ (𝔇.A X) :=
  Algebra.compHom (𝔇.A X) (algebraMap ℚ F)

/-- The `𝐐`-action on `A(X)` is the `F`-action through `𝐐 ⊆ F`. -/
theorem rat_smul_A {X : (SmoothProjectiveScheme k).FullSubcategory} (q : ℚ) (a : 𝔇.A X) :
    q • a = (algebraMap ℚ F q) • a := rfl

/-- The `𝐐`-algebra structure of `A(X)`, read in the standing situation
`Stacks.WeilCohomology.FirstChernClassData.toChernSetup`. -/
instance algebraRatToChernSetup (hA1 : 𝔇.CoproductAxiom) (hA3 : 𝔇.ProjectiveBundleAxiom)
    (X : (SmoothProjectiveScheme k).FullSubcategory) :
    Algebra ℚ ((𝔇.toChernSetup hA1 hA3).A X) :=
  𝔇.algebraRatA X

/-- (D1) read for `A`: the graded pieces of `A` are `𝐐`-subspaces, being `F`-subspaces. -/
theorem isRationallyGraded (hA1 : 𝔇.CoproductAxiom) (hA3 : 𝔇.ProjectiveBundleAxiom) :
    (𝔇.toChernSetup hA1 hA3).IsRationallyGraded := fun X i q _ ha =>
  (𝔇.grade X (2 * (i : ℤ))).smul_mem (algebraMap ℚ F q) ha

/-! ### Tag 0FIE -/

/-- The twisted rule attached to a rule with values in `∏_{i ≥ 0} A^i(X)`: the `n`-th component,
read back through the coordinates in `H^*(X)(n)`. -/
def twistRule {X : (SmoothProjectiveScheme k).FullSubcategory} (φ : PowerSeries (𝔇.A X)) :
    ∀ n : ℕ, tateTwist F 𝔇.tate (𝔇.H X) n :=
  fun n => (𝔇.κ X n).symm ((PowerSeries.coeff n φ : 𝔇.A X) : 𝔇.H X)

omit [CharZero F] in
/-- The coordinates of the `n`-th component of `𝔇.twistRule φ` are the `n`-th coefficient of
`φ`. -/
theorem κ_twistRule {X : (SmoothProjectiveScheme k).FullSubcategory} (φ : PowerSeries (𝔇.A X))
    (n : ℕ) : 𝔇.κ X n (𝔇.twistRule φ n) = ((PowerSeries.coeff n φ : 𝔇.A X) : 𝔇.H X) :=
  LinearEquiv.apply_symm_apply _ _

omit [CharZero F] in
/-- A power series over `A(X)` is determined by the twisted rule it names. -/
theorem twistRule_injective (X : (SmoothProjectiveScheme k).FullSubcategory) :
    Function.Injective (𝔇.twistRule (X := X)) := fun φ ψ h => PowerSeries.ext fun n =>
  Subtype.ext (by rw [← 𝔇.κ_twistRule, ← 𝔇.κ_twistRule, h])

omit [CharZero F] in
/-- `Stacks.WeilCohomology.FirstChernClassData.twistRule` is additive. -/
theorem twistRule_add {X : (SmoothProjectiveScheme k).FullSubcategory} (φ ψ : PowerSeries (𝔇.A X)) :
    𝔇.twistRule (φ + ψ) = 𝔇.twistRule φ + 𝔇.twistRule ψ := funext fun n => by
  simp [twistRule]

omit [CharZero F] in
/-- The coordinates of a cup product of two families: `(a ∪ b)_n = ∑_{i + j = n} a_i ∪ b_j`. -/
theorem κ_cupConv (X : (SmoothProjectiveScheme k).FullSubcategory)
    (a b : ∀ n : ℕ, tateTwist F 𝔇.tate (𝔇.H X) n) (n : ℕ) :
    𝔇.κ X n (𝔇.cupConv X a b n) =
      ∑ i : Fin (n + 1), 𝔇.κ X i (a i) * 𝔇.κ X (n - i : ℕ) (b (n - i)) := by
  rw [cupConv, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact 𝔇.κ_tateCup X _ _ _ _ _ _

omit [CharZero F] in
/-- `Stacks.WeilCohomology.FirstChernClassData.twistRule` sends `0` to `0`. -/
theorem twistRule_zero (X : (SmoothProjectiveScheme k).FullSubcategory) :
    𝔇.twistRule (0 : PowerSeries (𝔇.A X)) = 0 := funext fun n => by
  simp [twistRule]

omit [CharZero F] in
/-- `Stacks.WeilCohomology.FirstChernClassData.twistRule` carries multiplication of power series
to the cup product `Stacks.WeilCohomology.FirstChernClassData.cupConv`. -/
theorem twistRule_mul {X : (SmoothProjectiveScheme k).FullSubcategory} (φ ψ : PowerSeries (𝔇.A X)) :
    𝔇.twistRule (φ * ψ) = 𝔇.cupConv X (𝔇.twistRule φ) (𝔇.twistRule ψ) := funext fun n => by
  apply (𝔇.κ X n).injective
  rw [κ_cupConv, κ_twistRule, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, ← Fin.sum_univ_eq_sum_range,
    AddSubmonoidClass.coe_finset_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [κ_twistRule, κ_twistRule, MulMemClass.coe_mul]

omit [CharZero F] in
/-- `Stacks.WeilCohomology.FirstChernClassData.twistRule` sends `1` to the unit
`Stacks.WeilCohomology.FirstChernClassData.oneConv` of the cup product. -/
theorem twistRule_one (X : (SmoothProjectiveScheme k).FullSubcategory) :
    𝔇.twistRule (1 : PowerSeries (𝔇.A X)) = 𝔇.oneConv X := funext fun n => by
  apply (𝔇.κ X n).injective
  rw [κ_twistRule, PowerSeries.coeff_one]
  rcases n with _ | n
  · rw [if_pos rfl, OneMemClass.coe_one]
    exact (𝔇.κ_unitTw X).symm
  · rw [if_neg (Nat.succ_ne_zero n), ZeroMemClass.coe_zero, oneConv,
      Pi.single_eq_of_ne (Nat.succ_ne_zero n), map_zero]

omit [CharZero F] in
/-- Twisting is compatible with pullback: applying `f^*` to the coefficients of `φ` names the
pullback of the twisted rule of `φ`. -/
theorem twistRule_map {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y)
    (φ : PowerSeries (𝔇.A Y)) (n : ℕ) :
    𝔇.twistRule (PowerSeries.map (𝔇.pullA f).toRingHom φ) n = 𝔇.pullTw f n (𝔇.twistRule φ n) := by
  apply (𝔇.κ X n).injective
  rw [κ_twistRule, κ_pullTw, κ_twistRule, PowerSeries.coeff_map]
  rfl

omit [CharZero F] in
/-- The twisted rule of `exp(c₁^A(ℒ))` is `exp(c₁^H(ℒ))`. -/
theorem twistRule_exp [CharZero F] (hA1 : 𝔇.CoproductAxiom) (hA3 : 𝔇.ProjectiveBundleAxiom)
    (X : (SmoothProjectiveScheme k).FullSubcategory) (L : ((toScheme k).obj X).picardGroup) :
    𝔇.twistRule (Weak.expFirstChernClass (𝔇.toChernSetup hA1 hA3) X L : PowerSeries (𝔇.A X)) =
      𝔇.expTw X (𝔇.c₁ X L) := funext fun n => by
  apply (𝔇.κ X n).injective
  refine (𝔇.κ_twistRule _ n).trans ?_
  refine (congrArg (fun z : 𝔇.A X => (z : 𝔇.H X))
    (Weak.coeff_expFirstChernClass (𝔚 := 𝔇.toChernSetup hA1 hA3) X L n)).trans ?_
  rw [expTw, map_smul, κ_twistPow]
  show ((algebraMap F (𝔇.A X) (algebraMap ℚ F ((n.factorial : ℚ)⁻¹)) *
    𝔇.c₁A X L ^ n : 𝔇.A X) : 𝔇.H X) = _
  rw [MulMemClass.coe_mul, SubmonoidClass.coe_pow, coe_c₁A, Algebra.algebraMap_eq_smul_one,
    Subalgebra.coe_smul, OneMemClass.coe_one, smul_one_mul, map_inv₀, map_natCast]

omit [CharZero F] in
/-- **Stacks Project, Tag 0FIE.** Assume given data (D0), (D1), (D2') satisfying axioms (A1),
(A2), (A3) and (A4). There is a unique rule which assigns to every smooth projective `X` over `k`
a ring homomorphism

`ch^H : K₀(Vect(X)) ⟶ ∏_{i ≥ 0} H^{2i}(X)(i)`

compatible with pullbacks such that `ch^H(ℒ) = exp(c₁^H(ℒ))` for every invertible
`𝒪_X`-module `ℒ`.

The twists are the tensor-defined ones, `Stacks.WeilCohomology.tateTwist`. A family
`(a_i)_{i ≥ 0}` with `a_i ∈ H^*(X)(i)` lies in `∏_{i ≥ 0} H^{2i}(X)(i)` when each `a_i` lies in the
image of `H^{2i}(X)(i)`. The ring structure of the product is the cup product
`Stacks.WeilCohomology.FirstChernClassData.cupConv`, `(a ∪ b)_n = ∑_{i + j = n} a_i ∪ b_j`, with
unit `Stacks.WeilCohomology.FirstChernClassData.oneConv`; a ring homomorphism is an additive,
multiplicative and unital map. Compatibility with pullbacks is `f^* ∘ ch^H = ch^H ∘ f^*`, the
pullback of `K₀(Vect(-))` being `AlgebraicGeometry.VectorBundleKZero.pullbackRingHom`, and
`exp(c₁^H(ℒ)) = ∑_n (1/n!) c₁^H(ℒ)^n` is `Stacks.WeilCohomology.FirstChernClassData.expTw`.

The proof is the source's: Proposition 45.12.4 (Tag 0FI9) for the category of smooth projective
schemes over `k`, the functor `A : X ↦ ⨁_{i ≥ 0} H^{2i}(X)(i)` and `c₁^H`, whose standing
assumptions are (A1)–(A4). The projective bundle formula is used in the weak form that (A3)
provides when `H^*` is nonzero in negative degrees; see the module documentation. -/
@[stacks 0FIE "under exactly (D0), (D1), (D2') and (A1)-(A4), for all smooth projective schemes \
  over k (not necessarily irreducible or nonempty), with the tensor-defined Tate twists: existence \
  and uniqueness of the rule K_0(Vect(X)) -> prod_{i >= 0} H^{2i}(X)(i), a ring homomorphism for \
  the cup product of the product. (D1) is Z-graded as in the chapter's conventions; the proof uses \
  condition (4) of Section 45.12 only through injectivity and the resolution of the top power, \
  which is what (A3) gives on A when H^* has negative-degree classes"]
theorem existsUnique_cohomologicalChernCharacter [CharZero F] (hA1 : 𝔇.CoproductAxiom)
    (hA2 : 𝔇.PullbackAxiom) (hA3 : 𝔇.ProjectiveBundleAxiom) (hA4 : 𝔇.DivisorAxiom) :
    ∃! ch : ∀ X : (SmoothProjectiveScheme k).FullSubcategory,
        VectorBundleKZero ((toScheme k).obj X) → ∀ n : ℕ, tateTwist F 𝔇.tate (𝔇.H X) n,
      (∀ X α (n : ℕ), ch X α n ∈
          LinearMap.range (tateTwistMap (L := 𝔇.tate) (𝔇.grade X (2 * (n : ℤ))).subtype n)) ∧
        (∀ X α β, ch X (α + β) = ch X α + ch X β) ∧
        (∀ X α β, ch X (α * β) = 𝔇.cupConv X (ch X α) (ch X β)) ∧
        (∀ X, ch X 1 = 𝔇.oneConv X) ∧
        (∀ {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y) α (n : ℕ),
          ch X (VectorBundleKZero.pullbackRingHom ((toScheme k).map f) α) n =
            𝔇.pullTw f n (ch Y α n)) ∧
          ∀ X (L : ((toScheme k).obj X).Modules)
            (hL : AlgebraicGeometry.SheafOfModules.IsInvertible ((toScheme k).obj X).presheaf
              ((toScheme k).obj X).ringCatSheaf.2 L),
            ch X (VectorBundleKZero.classOf _ L) = 𝔇.expTw X (𝔇.c₁ X (picardClassOf _ L hL)) := by
  obtain ⟨ch, -, hgr, hpull, hinv⟩ :=
    Weak.exists_cohomologicalChernCharacter_of_source (𝔇.toChernSetup hA1 hA3)
    (𝔇.isRationallyGraded hA1 hA3) (𝔇.pullbackFirstChernCondition hA1 hA3 hA2)
    (𝔇.bundleCompareClause hA1 hA3) (𝔇.divisorDatumClause hA1 hA3 hA4)
  -- the constructed rule, read with values in `∏_{i ≥ 0} A^i(X)`
  let ch₀ : ∀ X, VectorBundleKZero ((toScheme k).obj X) →+* PowerSeries (𝔇.A X) := ch
  have hgr₀ : ∀ X α (n : ℕ),
      ((PowerSeries.coeff n (ch₀ X α) : 𝔇.A X) : 𝔇.H X) ∈ 𝔇.grade X (2 * (n : ℤ)) :=
    fun X α n => Weak.mem_gradedPowerSeries.mp (hgr X α) n
  have hpull₀ : ∀ {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y) α,
      PowerSeries.map (𝔇.pullA f).toRingHom (ch₀ Y α) =
        ch₀ X (VectorBundleKZero.pullbackRingHom ((toScheme k).map f) α) := fun f α => hpull f α
  have hinv₀ : ∀ X (L : ((toScheme k).obj X).Modules)
      (hL : AlgebraicGeometry.SheafOfModules.IsInvertible ((toScheme k).obj X).presheaf
        ((toScheme k).obj X).ringCatSheaf.2 L),
      ch₀ X (VectorBundleKZero.classOf _ L) =
        (Weak.expFirstChernClass (𝔇.toChernSetup hA1 hA3) X (picardClassOf _ L hL) :
          PowerSeries (𝔇.A X)) := hinv
  refine ⟨fun X α => 𝔇.twistRule (ch₀ X α),
    ⟨fun X α n => ?_, fun X α β => ?_, fun X α β => ?_, fun X => ?_, fun f α n => ?_,
      fun X L hL => ?_⟩, ?_⟩
  · show 𝔇.twistRule (ch₀ X α) n ∈ _
    rw [mem_range_tateTwistMap_iff, κ_twistRule]
    exact hgr₀ X α n
  · show 𝔇.twistRule (ch₀ X (α + β)) = _
    rw [map_add]
    exact 𝔇.twistRule_add _ _
  · show 𝔇.twistRule (ch₀ X (α * β)) = _
    rw [map_mul]
    exact 𝔇.twistRule_mul _ _
  · show 𝔇.twistRule (ch₀ X 1) = _
    rw [map_one]
    exact 𝔇.twistRule_one X
  · show 𝔇.twistRule (ch₀ _ (VectorBundleKZero.pullbackRingHom _ α)) n = _
    rw [← hpull₀ f α]
    exact 𝔇.twistRule_map f _ n
  · show 𝔇.twistRule (ch₀ X _) = _
    rw [hinv₀ X L hL]
    exact 𝔇.twistRule_exp hA1 hA3 X _
  · rintro ch' ⟨hgr', hadd', hmul', hone', hpull', hinv'⟩
    -- the rule with values in `∏_{i ≥ 0} A^i(X)` read off `ch'` in coordinates
    let lift : ∀ X, VectorBundleKZero ((toScheme k).obj X) → PowerSeries (𝔇.A X) := fun X α =>
      PowerSeries.mk fun n => ⟨𝔇.κ X n (ch' X α n), mem_evenPart_of_mem _
        ((𝔇.mem_range_tateTwistMap_iff _ _ _).mp (hgr' X α n))⟩
    have hlift : ∀ X α, 𝔇.twistRule (lift X α) = ch' X α := fun X α => funext fun n => by
      apply (𝔇.κ X n).injective
      rw [κ_twistRule, PowerSeries.coeff_mk]
    have h0 : ∀ X, ch' X 0 = 0 := fun X => by simpa using hadd' X 0 0
    let ψ : ∀ X, VectorBundleKZero ((toScheme k).obj X) →+* PowerSeries (𝔇.A X) := fun X =>
      { toFun := lift X
        map_one' := 𝔇.twistRule_injective X (by rw [hlift, hone', twistRule_one])
        map_mul' := fun α β => 𝔇.twistRule_injective X (by
          rw [hlift, hmul', twistRule_mul, hlift, hlift])
        map_zero' := 𝔇.twistRule_injective X (by rw [hlift, h0, twistRule_zero])
        map_add' := fun α β => 𝔇.twistRule_injective X (by
          rw [hlift, hadd', twistRule_add, hlift, hlift]) }
    have hψ : ∀ X α, 𝔇.twistRule (ψ X α) = ch' X α := hlift
    have hpullψ : ∀ {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y) α,
        PowerSeries.map (𝔇.pullA f).toRingHom (ψ Y α) =
          ψ X (VectorBundleKZero.pullbackRingHom ((toScheme k).map f) α) := fun f α =>
      𝔇.twistRule_injective _ (funext fun n => by
        rw [twistRule_map, hψ, hψ, hpull'])
    have hinvψ : ∀ X (L : ((toScheme k).obj X).Modules)
        (hL : AlgebraicGeometry.SheafOfModules.IsInvertible ((toScheme k).obj X).presheaf
          ((toScheme k).obj X).ringCatSheaf.2 L),
        ψ X (VectorBundleKZero.classOf _ L) =
          (Weak.expFirstChernClass (𝔇.toChernSetup hA1 hA3) X (picardClassOf _ L hL) :
            PowerSeries (𝔇.A X)) :=
      fun X L hL => 𝔇.twistRule_injective _ (by rw [hψ, hinv' X L hL, twistRule_exp])
    have heq : ∀ X α, ψ X α = ch₀ X α := fun X α =>
      Weak.eq_of_cohomologicalChernCharacter' (𝔇.toChernSetup hA1 hA3) (ch := ψ) (ch' := ch)
        hpullψ hpull hinvψ hinv X α
    funext X α
    rw [← hψ, heq]

end FirstChernClassData

end Stacks.WeilCohomology

end
