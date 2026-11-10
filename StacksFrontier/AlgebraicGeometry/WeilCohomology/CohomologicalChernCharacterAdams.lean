module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.WeilChernCharacter
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.WeakChernClasses.AdamsEigenvalues

/-!
# The cohomological Chern character of a Weil cohomology theory and the second Adams operator

Given data (D0), (D1), (D2') satisfying axioms (A1)–(A4) of Section 45.14, Tag 0FIE produces a
unique rule `ch^H : K₀(Vect(X)) ⟶ ∏_{i ≥ 0} H^{2i}(X)(i)` with the properties listed there. This
file names those properties,
`Stacks.WeilCohomology.FirstChernClassData.IsCohomologicalChernCharacter`, and proves that such a
rule satisfies the identity of Tag 0FIA,

  `ch^H_n(ψ²(α)) = 2^n ch^H_n(α)`,

for the second Adams operator `ψ²` of Tag 0FEJ. This is the input of the grading argument in the
proof of Tag 0FIF.

The identity is `Stacks.WeilCohomology.Weak.coeff_secondAdams`, read through the coordinates
`H^*(X)(n) ≅ H^*(X)`: the rule is lifted to ring maps into `∏_{i ≥ 0} A^i(X)` for
`A(X) = ⨁_{i ≥ 0} H^{2i}(X)`, exactly as in the uniqueness half of Tag 0FIE.

## Main definitions

* `Stacks.WeilCohomology.FirstChernClassData.IsCohomologicalChernCharacter` — the properties of
  Tag 0FIE.

## Main results

* `Stacks.WeilCohomology.FirstChernClassData.existsUnique_isCohomologicalChernCharacter` — Tag 0FIE
  in terms of the predicate.
* `Stacks.WeilCohomology.FirstChernClassData.IsCohomologicalChernCharacter.lift` — the rule as ring
  maps into `∏_{i ≥ 0} A^i(X)`.
* `Stacks.WeilCohomology.FirstChernClassData.IsCohomologicalChernCharacter.secondAdams` —
  `ch^H_n(ψ²(α)) = 2^n ch^H_n(α)`.

## References

* [Stacks Project, Tag 0FIE](https://stacks.math.columbia.edu/tag/0FIE)
* [Stacks Project, Tag 0FIA](https://stacks.math.columbia.edu/tag/0FIA)
* [Stacks Project, Tag 0FEJ](https://stacks.math.columbia.edu/tag/0FEJ)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u w

namespace Stacks.WeilCohomology

open SmoothProjectiveScheme

namespace FirstChernClassData

variable {k : Type u} [Field k] {F : Type w} [Field F] (𝔇 : FirstChernClassData k F)

/-- **The properties of the cohomological Chern character of Tag 0FIE.** A rule `ch` assigning to
every smooth projective `X` over `k` and every `α ∈ K₀(Vect(X))` a family
`(ch X α n)_{n ≥ 0}`, `ch X α n ∈ H^{2n}(X)(n)`, which is a ring homomorphism into
`∏_{i ≥ 0} H^{2i}(X)(i)` with the cup product `Stacks.WeilCohomology.FirstChernClassData.cupConv`,
is compatible with pullbacks, and sends an invertible module `ℒ` to `exp(c₁^H(ℒ))`. These are the
properties of `Stacks.WeilCohomology.FirstChernClassData.existsUnique_cohomologicalChernCharacter`,
verbatim. -/
def IsCohomologicalChernCharacter
    (ch : ∀ X : (SmoothProjectiveScheme k).FullSubcategory,
      VectorBundleKZero ((toScheme k).obj X) → ∀ n : ℕ, tateTwist F 𝔇.tate (𝔇.H X) n) : Prop :=
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
        ch X (VectorBundleKZero.classOf _ L) = 𝔇.expTw X (𝔇.c₁ X (picardClassOf _ L hL))

variable [CharZero F]

/-- **Tag 0FIE**, in terms of `IsCohomologicalChernCharacter`: under (A1)–(A4) exactly one rule
has the properties of Tag 0FIE. -/
theorem existsUnique_isCohomologicalChernCharacter (hA1 : 𝔇.CoproductAxiom)
    (hA2 : 𝔇.PullbackAxiom) (hA3 : 𝔇.ProjectiveBundleAxiom) (hA4 : 𝔇.DivisorAxiom) :
    ∃! ch, 𝔇.IsCohomologicalChernCharacter ch :=
  𝔇.existsUnique_cohomologicalChernCharacter hA1 hA2 hA3 hA4

variable {𝔇}
  {ch : ∀ X : (SmoothProjectiveScheme k).FullSubcategory,
    VectorBundleKZero ((toScheme k).obj X) → ∀ n : ℕ, tateTwist F 𝔇.tate (𝔇.H X) n}

namespace IsCohomologicalChernCharacter

omit [CharZero F] in
/-- A cohomological Chern character sends the zero class to zero. -/
theorem apply_zero (h : 𝔇.IsCohomologicalChernCharacter ch) (X) : ch X 0 = 0 := by
  simpa using h.2.1 X 0 0

/-- **The rule read in coordinates**: `ch^H` as ring maps `K₀(Vect(X)) ⟶ ∏_{i ≥ 0} A^i(X)` for
`A(X) = ⨁_{i ≥ 0} H^{2i}(X)`, the coordinate of `ch X α n ∈ H^{2n}(X)(n)` in `H^{2n}(X)` being the
`n`-th coefficient. -/
def lift (h : 𝔇.IsCohomologicalChernCharacter ch) (X : (SmoothProjectiveScheme k).FullSubcategory) :
    VectorBundleKZero ((toScheme k).obj X) →+* PowerSeries (𝔇.A X) :=
  have hlift : ∀ α, 𝔇.twistRule (PowerSeries.mk fun n => (⟨𝔇.κ X n (ch X α n),
      mem_evenPart_of_mem _ ((𝔇.mem_range_tateTwistMap_iff _ _ _).mp (h.1 X α n))⟩ :
        𝔇.A X)) = ch X α := fun α => funext fun n => by
    apply (𝔇.κ X n).injective
    rw [κ_twistRule, PowerSeries.coeff_mk]
  { toFun := fun α => PowerSeries.mk fun n => ⟨𝔇.κ X n (ch X α n),
      mem_evenPart_of_mem _ ((𝔇.mem_range_tateTwistMap_iff _ _ _).mp (h.1 X α n))⟩
    map_one' := 𝔇.twistRule_injective X (by rw [hlift, h.2.2.2.1, twistRule_one])
    map_mul' := fun α β => 𝔇.twistRule_injective X (by
      rw [hlift, h.2.2.1, twistRule_mul, hlift, hlift])
    map_zero' := 𝔇.twistRule_injective X (by rw [hlift, h.apply_zero, twistRule_zero])
    map_add' := fun α β => 𝔇.twistRule_injective X (by
      rw [hlift, h.2.1, twistRule_add, hlift, hlift]) }

omit [CharZero F] in
/-- The `n`-th coefficient of the rule in coordinates is the coordinate of `ch X α n` in
`H^{2n}(X)`. -/
theorem coeff_lift (h : 𝔇.IsCohomologicalChernCharacter ch) (X) (α) (n : ℕ) :
    ((PowerSeries.coeff n (h.lift X α) : 𝔇.A X) : 𝔇.H X) = 𝔇.κ X n (ch X α n) := by
  simp [lift]

omit [CharZero F] in
/-- The coordinates of the rule give back the rule. -/
theorem twistRule_lift (h : 𝔇.IsCohomologicalChernCharacter ch) (X) (α) :
    𝔇.twistRule (h.lift X α) = ch X α := funext fun n => by
  apply (𝔇.κ X n).injective
  rw [κ_twistRule, coeff_lift]

omit [CharZero F] in
/-- The `n`-th coefficient of the rule in coordinates lies in `A^n(X) = H^{2n}(X)`. -/
theorem coeff_lift_mem (h : 𝔇.IsCohomologicalChernCharacter ch) (X) (α) (n : ℕ) :
    PowerSeries.coeff n (h.lift X α) ∈ evenGrade (𝔇.grade X) n := by
  rw [mem_evenGrade, coeff_lift]
  exact (𝔇.mem_range_tateTwistMap_iff _ _ _).mp (h.1 X α n)

omit [CharZero F] in
/-- The rule in coordinates is compatible with pullbacks. -/
theorem map_lift (h : 𝔇.IsCohomologicalChernCharacter ch) {X Y} (f : X ⟶ Y) (α) :
    PowerSeries.map (𝔇.pullA f).toRingHom (h.lift Y α) =
      h.lift X (VectorBundleKZero.pullbackRingHom ((toScheme k).map f) α) :=
  𝔇.twistRule_injective _ (funext fun n => by
    rw [twistRule_map, twistRule_lift, twistRule_lift, h.2.2.2.2.1])

/-- The rule in coordinates takes the value `exp(c₁^A(ℒ))` on an invertible module. -/
theorem lift_classOf (h : 𝔇.IsCohomologicalChernCharacter ch) (hA1 : 𝔇.CoproductAxiom)
    (hA3 : 𝔇.ProjectiveBundleAxiom) (X) (L : ((toScheme k).obj X).Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible ((toScheme k).obj X).presheaf
      ((toScheme k).obj X).ringCatSheaf.2 L) :
    h.lift X (VectorBundleKZero.classOf _ L) =
      Weak.expFirstChernClass (𝔇.toChernSetup hA1 hA3) X (picardClassOf _ L hL) :=
  𝔇.twistRule_injective _ (by rw [twistRule_lift, h.2.2.2.2.2 X L hL, twistRule_exp])

/-- **Tag 0FIA for the rule in coordinates**: `ch^A_n(ψ²(α)) = 2^n ch^A_n(α)`. -/
theorem coeff_lift_secondAdams (h : 𝔇.IsCohomologicalChernCharacter ch)
    (hA1 : 𝔇.CoproductAxiom) (hA3 : 𝔇.ProjectiveBundleAxiom) (X) (α) (n : ℕ) :
    PowerSeries.coeff n (h.lift X (VectorBundleKZero.secondAdamsRingHom
        (VectorBundleKZero.squarePowersData ((toScheme k).obj X)) α)) =
      (2 ^ n : ℕ) • PowerSeries.coeff n (h.lift X α) :=
  Weak.coeff_secondAdams (𝔚 := 𝔇.toChernSetup hA1 hA3) (ch := h.lift) (fun f α => h.map_lift f α)
    (fun X L hL => h.lift_classOf hA1 hA3 X L hL) X α n

/-- **Tag 0FIA for the cohomological Chern character of Tag 0FIE.** A rule with the properties of
Tag 0FIE satisfies `ch^H_n(ψ²(α)) = 2^n ch^H_n(α)` for every `α ∈ K₀(Vect(X))`, `ψ²` being the
second Adams operator `AlgebraicGeometry.VectorBundleKZero.secondAdamsRingHom` of Tag 0FEJ. -/
theorem secondAdams (h : 𝔇.IsCohomologicalChernCharacter ch) (hA1 : 𝔇.CoproductAxiom)
    (hA3 : 𝔇.ProjectiveBundleAxiom) (X : (SmoothProjectiveScheme k).FullSubcategory)
    (α : VectorBundleKZero ((toScheme k).obj X)) (n : ℕ) :
    ch X (VectorBundleKZero.secondAdamsRingHom
        (VectorBundleKZero.squarePowersData ((toScheme k).obj X)) α) n =
      (2 ^ n : ℕ) • ch X α n := by
  apply (𝔇.κ X n).injective
  rw [← coeff_lift h, map_nsmul, ← coeff_lift h, h.coeff_lift_secondAdams hA1 hA3]
  exact AddSubmonoidClass.coe_nsmul _ _

end IsCohomologicalChernCharacter

end FirstChernClassData

end Stacks.WeilCohomology

end
