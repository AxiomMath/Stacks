module

public import StacksFrontier.AlgebraicGeometry.Chow.DivisorTransport.Order
public import StacksFrontier.AlgebraicGeometry.Curves.BombieriStepanov.Residue
public import StacksFrontier.AlgebraicGeometry.Curves.BombieriStepanov.SmoothUpperBound
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.ClosedPointCodimension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ClosedPointDegree
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.PointCountMonotone

/-!
# A Frobenius-semilinear automorphism of a curve has finitely many fixed points

Let `C` be a smooth proper curve over an algebraically closed field `Ω` of characteristic `p`
and let `Ψ` be an automorphism of the scheme `C` which is `Q`-semilinear for `Q = p ^ n`,
`n ≥ 1`: `Ψ ≫ g = g ≫ Spec(c ↦ c ^ Q)`, `g : C ⟶ Spec Ω` the structure morphism. (For `C` the
base change of a curve over `𝔽_Q`, `Ψ` is the arithmetic Frobenius.) **The closed points fixed
by `Ψ` form a finite set.**

The argument uses only the function field `K` of `C`. Pullback along `Ψ` is a field
automorphism `τ` of `K`, raising constants to the `Q`-th power and moving orders of vanishing:
`ord_x (τ h) = ord_{Ψ x} h`. At a fixed point `x`, a function `a` regular at `x` is congruent
to a constant `c` modulo the maximal ideal (the residue field is `Ω`), hence so are `τ a` and
`a ^ Q`, to `c ^ Q`: the function `b = τ a - a ^ Q` vanishes at every fixed point at which `a`
is regular. And `τ a ≠ a ^ Q` for some `a`: otherwise `τ` would be the `Q`-power map and `K`
would be perfect, which a uniformizer at a closed point forbids. A nonzero function has finitely
many zeros and poles.

## Main results

* `Stacks.Zeta.functionFieldRingEquivOfIso_symm_algebraMap`: `τ c = c ^ Q` on constants.
* `Stacks.Zeta.finite_setOf_isClosed_fixed`: the finiteness.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Order

universe u

namespace Stacks.Zeta

section Constants

variable {Ω : Type u} [Field Ω]

/-- The structural map `Ω → 𝒪_{X, x}` is natural along morphisms of schemes over `Ω`. -/
theorem fieldToStalk_comp_stalkMap {X Y : Scheme.{u}} (e : X ⟶ Y) (gY : Y ⟶ Spec (.of Ω))
    (x : X) : fieldToStalk gY (e.base x) ≫ e.stalkMap x = fieldToStalk (e ≫ gY) x := by
  have h : Y.presheaf.germ ⊤ (e.base x) trivial ≫ e.stalkMap x =
      e.appTop ≫ X.presheaf.germ ⊤ x trivial :=
    Scheme.Hom.germ_stalkMap e ⊤ x trivial
  simp only [fieldToStalk, Scheme.Hom.comp_appTop, Category.assoc]
  rw [h]

/-- The structural map `Ω → 𝒪_{X, x}` of `X` over `Spec Ω` twisted by a ring endomorphism `F`
of `Ω` is `F` followed by the structural map. -/
theorem fieldToStalk_comp_specMap {X : Scheme.{u}} (g : X ⟶ Spec (.of Ω)) (F : Ω →+* Ω)
    (x : X) :
    fieldToStalk (g ≫ Spec.map (CommRingCat.ofHom F)) x =
      CommRingCat.ofHom F ≫ fieldToStalk g x := by
  simp only [fieldToStalk, Scheme.Hom.comp_appTop, Scheme.ΓSpecIso_inv_naturality_assoc,
    Category.assoc]

variable {C : Scheme.{u}} [IsIntegral C] (g : C ⟶ Spec (.of Ω)) (Ψ : C ≅ C) (F : Ω →+* Ω)
  (hΨ : Ψ.hom ≫ g = g ≫ Spec.map (CommRingCat.ofHom F))

include hΨ in
/-- **Transport along a semilinear automorphism undoes `F` on constants.** The automorphism
`σ` of the function field induced by `Ψ` (pushforward of functions) satisfies
`σ (F c) = c`. -/
theorem functionFieldRingEquivOfIso_algebraMap_apply (c : Ω) :
    letI := Stacks.BombieriStepanov.functionFieldAlgebra g
    Stacks.Chow.functionFieldRingEquivOfIso Ψ (algebraMap Ω C.functionField (F c)) =
      algebraMap Ω C.functionField c := by
  let := Stacks.BombieriStepanov.functionFieldAlgebra g
  set η := genericPoint C
  rw [Stacks.BombieriStepanov.algebraMap_functionFieldAlgebra g η,
    Stacks.Chow.functionFieldRingEquivOfIso_algebraMap,
    Stacks.BombieriStepanov.algebraMap_functionFieldAlgebra g (Ψ.hom.base η)]
  congr 1
  have h : (fieldToStalk g η).hom (F c) =
      Ψ.hom.stalkMap η ((fieldToStalk g (Ψ.hom.base η)).hom c) := by
    rw [← CommRingCat.comp_apply, fieldToStalk_comp_stalkMap, hΨ, fieldToStalk_comp_specMap]
    rfl
  rw [h, Stacks.Chow.stalkRingEquivOfIso_apply, Stacks.Chow.stalkIsoOfIso_hom_stalkMap_apply]

include hΨ in
/-- **Pullback along a semilinear automorphism applies `F` to constants.** -/
theorem functionFieldRingEquivOfIso_symm_algebraMap (c : Ω) :
    letI := Stacks.BombieriStepanov.functionFieldAlgebra g
    (Stacks.Chow.functionFieldRingEquivOfIso Ψ).symm (algebraMap Ω C.functionField c) =
      algebraMap Ω C.functionField (F c) := by
  let := Stacks.BombieriStepanov.functionFieldAlgebra g
  rw [RingEquiv.symm_apply_eq, functionFieldRingEquivOfIso_algebraMap_apply g Ψ F hΨ]

variable [IsLocallyNoetherian C] in
/-- Pullback along an automorphism moves orders of vanishing: `ord_x (τ h) = ord_{Ψ x} h`. -/
theorem ord_functionFieldRingEquivOfIso_symm (h : C.functionField) (x : C) :
    C.ord ((Stacks.Chow.functionFieldRingEquivOfIso Ψ).symm h) x = C.ord h (Ψ.hom.base x) := by
  conv_rhs => rw [← (Stacks.Chow.functionFieldRingEquivOfIso Ψ).apply_symm_apply h]
  rw [Stacks.Chow.ord_functionFieldRingEquivOfIso]

end Constants

section Curve

variable {Ω : Type u} [Field Ω] [IsAlgClosed Ω] {C : Scheme.{u}} (g : C ⟶ Spec (.of Ω))
  [IsProper g] [Smooth g] [IsCurve Ω g]

omit [IsAlgClosed Ω] [IsProper g] [Smooth g] in
include g in
/-- The generic point of a curve is not closed. -/
theorem ne_genericPoint_of_isClosed {x : C} (hx : IsClosed ({x} : Set C)) :
    x ≠ genericPoint C := by
  rintro rfl
  have huniv : (Set.univ : Set C) = {genericPoint C} := by
    rw [← hx.closure_eq]
    exact (genericPoint_spec C).symm
  have hsub : Subsingleton C := ⟨fun a b => by
    have ha : a ∈ ({genericPoint C} : Set C) := huniv ▸ Set.mem_univ a
    have hb : b ∈ ({genericPoint C} : Set C) := huniv ▸ Set.mem_univ b
    rw [Set.mem_singleton_iff] at ha hb
    rw [ha, hb]⟩
  have h1 := IsCurve.topologicalKrullDim_eq_one (k := Ω) (f := g)
  have h2 := topologicalKrullDim_zero_of_discreteTopology C
  rw [h1] at h2
  exact absurd h2 (by decide)

omit [IsAlgClosed Ω] [IsProper g] [Smooth g] in
include g in
/-- A closed point of a curve has coheight one. -/
theorem coheight_eq_one_of_isClosed {x : C} (hx : IsClosed ({x} : Set C)) : coheight x = 1 :=
  AlgebraicGeometry.IsCurve.coheight_eq_one g (ne_genericPoint_of_isClosed g hx)

omit [IsProper g] [IsCurve Ω g] in
/-- At a closed point the structural map `Ω → κ(x)` is bijective. -/
theorem bijective_fieldToResidue {x : C} (hx : IsClosed ({x} : Set C)) :
    Function.Bijective (fieldToResidue g x).hom := by
  let : Algebra Ω (C.residueField x) := (fieldToResidue g x).hom.toAlgebra
  have : Algebra.FiniteType Ω (C.residueField x) :=
    Stacks.EtaleCohomology.finiteType_fieldToResidue g x hx
  have : Module.Finite Ω (C.residueField x) :=
    finite_of_finite_type_of_isJacobsonRing Ω (C.residueField x)
  exact IsAlgClosed.algebraMap_bijective_of_isIntegral (k := Ω) (K := C.residueField x)

omit [IsProper g] in
/-- **A function regular at a closed point is a constant plus a function vanishing there.** -/
theorem exists_one_le_ord_sub [IsLocallyNoetherian C] {x : C} (hx : IsClosed ({x} : Set C))
    {a : C.functionField} (ha : 0 ≤ C.ord a x) :
    letI := Stacks.BombieriStepanov.functionFieldAlgebra g
    ∃ c : Ω, a = algebraMap Ω C.functionField c ∨
      1 ≤ C.ord (a - algebraMap Ω C.functionField c) x := by
  let := Stacks.BombieriStepanov.functionFieldAlgebra g
  have hx1 := coheight_eq_one_of_isClosed g hx
  have := IsCurve.isDiscreteValuationRing_stalk_of_isClosed Ω g hx
  obtain ⟨s, rfl⟩ := Stacks.BombieriStepanov.exists_algebraMap_eq_of_ord_nonneg hx1 ha
  obtain ⟨c, hc⟩ := (bijective_fieldToResidue g hx).2 (C.residue x s)
  refine ⟨c, ?_⟩
  set d := s - (fieldToStalk g x).hom c with hd
  have hdm : d ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk x) := by
    rw [← IsLocalRing.residue_eq_zero_iff, hd, map_sub, sub_eq_zero]
    show C.residue x s = (fieldToStalk g x ≫ C.residue x).hom c
    exact hc.symm
  have heq : algebraMap (C.presheaf.stalk x) C.functionField s - algebraMap Ω C.functionField c =
      algebraMap (C.presheaf.stalk x) C.functionField d := by
    rw [Stacks.BombieriStepanov.algebraMap_functionFieldAlgebra g x c, hd, map_sub]
  rcases eq_or_ne d 0 with hd0 | hd0
  · left
    rw [← sub_eq_zero, heq, hd0, map_zero]
  · right
    rw [heq]
    exact Stacks.BombieriStepanov.one_le_ord_algebraMap hx1 hd0 hdm

end Curve

section Finite

variable {Ω : Type u} [Field Ω] [IsAlgClosed Ω] {C : Scheme.{u}} (g : C ⟶ Spec (.of Ω))
  [IsProper g] [Smooth g] [IsCurve Ω g] (p : ℕ) [hp : Fact p.Prime] [CharP Ω p] (n : ℕ)
  (hn : 0 < n) (Ψ : C ≅ C)
  (hΨ : Ψ.hom ≫ g = g ≫ Spec.map (CommRingCat.ofHom (iterateFrobenius Ω p n)))

/-- The order of a power. -/
theorem ord_pow' [IsIntegral C] [IsLocallyNoetherian C] {f : C.functionField} (hf : f ≠ 0)
    (x : C) (k : ℕ) : C.ord (f ^ k) x = k * C.ord f x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Scheme.ord_mul (pow_ne_zero _ hf) hf, ih]
    push_cast
    ring

include hn hΨ in
/-- **The closed points fixed by a Frobenius-semilinear automorphism of a smooth proper curve
form a finite set.** -/
theorem finite_setOf_isClosed_fixed :
    {x : C | IsClosed ({x} : Set C) ∧ Ψ.hom.base x = x}.Finite := by
  classical
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian g
  let := Stacks.BombieriStepanov.functionFieldAlgebra g
  set K := C.functionField
  set τ := (Stacks.Chow.functionFieldRingEquivOfIso Ψ).symm
  set Q := p ^ n with hQ
  have hQ2 : 2 ≤ Q := Nat.one_lt_pow hn.ne' hp.out.one_lt
  have : CharP K p := charP_of_injective_algebraMap (algebraMap Ω K).injective p
  have hτc : ∀ c : Ω, τ (algebraMap Ω K c) = algebraMap Ω K c ^ Q := fun c => by
    rw [functionFieldRingEquivOfIso_symm_algebraMap g Ψ _ hΨ, iterateFrobenius_def, map_pow]
  have hτord : ∀ (h : K) (x : C), C.ord (τ h) x = C.ord h (Ψ.hom.base x) :=
    ord_functionFieldRingEquivOfIso_symm Ψ
  have hdvr : ∀ x : C, coheight x = 1 → IsDiscreteValuationRing (C.presheaf.stalk x) :=
    fun x hx => Stacks.BombieriStepanov.isDiscreteValuationRing_stalk_of_coheight_eq_one g x hx
  -- some function is not sent to its `Q`-th power
  obtain ⟨a, ha⟩ : ∃ a : K, τ a ≠ a ^ Q := by
    by_contra hall
    push Not at hall
    obtain ⟨z, hz⟩ := (Stacks.EtaleCohomology.infinite_closedPoints_of_isCurve (f := g)).nonempty
    have hz1 : coheight z = 1 := coheight_eq_one_of_isClosed g hz
    have := hdvr z hz1
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (C.presheaf.stalk z)
    set u := algebraMap (C.presheaf.stalk z) K π
    have hu1 : C.ord u z = 1 := Stacks.BombieriStepanov.ord_algebraMap_irreducible hz1 hπ
    have hu0 : u ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hπ.ne_zero
    set w := τ.symm u
    have hw0 : w ≠ 0 := by simpa [w] using hu0
    have huw : u = w ^ Q := by rw [← hall w, RingEquiv.apply_symm_apply]
    rw [huw, ord_pow' hw0] at hu1
    have : (Q : ℤ) * C.ord w z = 1 := hu1
    have hQ' : (2 : ℤ) ≤ Q := by exact_mod_cast hQ2
    rcases lt_trichotomy (C.ord w z) 0 with h | h | h
    · nlinarith
    · rw [h] at this; simp at this
    · nlinarith
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp [zero_pow (by omega : Q ≠ 0)] at ha
  set b := τ a - a ^ Q
  have hb0 : b ≠ 0 := sub_ne_zero.2 ha
  have hD := Stacks.BombieriStepanov.hasDegreeFormula_curveVal hdvr Ω g
  refine ((hD.finite_support a ha0).union (hD.finite_support b hb0)).image Subtype.val
    |>.subset ?_
  rintro x ⟨hx, hfix⟩
  have hx1 : coheight x = 1 := coheight_eq_one_of_isClosed g hx
  have := hdvr x hx1
  refine ⟨⟨x, hx1⟩, ?_, rfl⟩
  simp only [Set.mem_union, Function.mem_support, Stacks.BombieriStepanov.ordZ_curveVal]
  by_cases hax : C.ord a x < 0
  · exact Or.inl hax.ne
  right
  obtain ⟨c, hc | hc⟩ := exists_one_le_ord_sub g hx (not_lt.1 hax)
  · exact absurd (by rw [hc, hτc]) ha
  set d := a - algebraMap Ω K c
  have hd0 : d ≠ 0 := fun h0 => by
    rw [h0] at hc
    simp at hc
  have hsub : d ^ Q = a ^ Q - algebraMap Ω K c ^ Q := by
    rw [hQ]; exact sub_pow_char_pow (R := K) a (algebraMap Ω K c) n
  have hbd : b = τ d - d ^ Q := by
    rw [hsub]
    simp only [b, d, map_sub, hτc]
    ring
  have h1 : 1 ≤ C.ord (τ d) x := by rw [hτord, hfix]; exact hc
  have h2 : 1 ≤ C.ord (-(d ^ Q)) x := by
    have : -(d ^ Q) = (-1) * d ^ Q := by ring
    rw [this, Scheme.ord_mul (by simp) (pow_ne_zero _ hd0), ord_pow' hd0]
    have hm1 : C.ord (-1 : K) x = 0 := by
      have := Scheme.ord_mul (x := x) (neg_ne_zero.2 (one_ne_zero (α := K)))
        (neg_ne_zero.2 (one_ne_zero (α := K)))
      rw [neg_one_mul, neg_neg, Stacks.BombieriStepanov.scheme_ord_one] at this
      omega
    rw [hm1, zero_add]
    have : (1 : ℤ) ≤ Q := by exact_mod_cast (by omega : 1 ≤ Q)
    nlinarith
  have h3 := Scheme.ord_add (x := x) (f := τ d) (g := -(d ^ Q)) (by rwa [← sub_eq_add_neg, ← hbd])
  rw [← sub_eq_add_neg, ← hbd] at h3
  omega

end Finite

end Stacks.Zeta

end
