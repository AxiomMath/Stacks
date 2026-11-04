module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Curves.IsNode
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinSchemes.Basic
import StacksFrontier.RingTheory.AdicCompletion.Flat
import StacksFrontier.RingTheory.Dualizing.Complex
import StacksFrontier.RingTheory.Dualizing.FlatLocalGorenstein
import StacksFrontier.RingTheory.Dualizing.ResidueFieldShift
import StacksFrontier.RingTheory.Dualizing.TrivialDuality
import StacksFrontier.RingTheory.Dualizing.TrivialDualityRing.Ext

/-!
# A multicross singularity of a Gorenstein scheme is a node

Let `k` be an algebraically closed field and `X` a scheme over `k`. A multicross singularity
`x ∈ X` has a completed local ring isomorphic to the multicross ring with `n ≥ 2` branches,
the subring of `k[[t]] × ⋯ × k[[t]]` of tuples with a common constant coefficient. If `X` is
Gorenstein then necessarily `n = 2`, that is, `x` is an ordinary double point.

The local ring at `x` is Gorenstein because `X` is, and its completion is Gorenstein because
completion is flat and local with regular closed fibre, so the criterion for a flat local
homomorphism applies. It therefore suffices to rule out `n ≥ 3` for the multicross ring `A`
itself. A Gorenstein local ring is a dualizing complex for itself, so derived Hom from its
residue field is a shift of the residue field; consequently `Ext¹(κ, A)` is at most
one-dimensional over `κ`, and any two of its elements satisfy a relation with a unit
coefficient. Applied to the classes obtained from the short exact sequence
`0 → 𝔪 → A → κ → 0` and the two coordinate projections `𝔪 → A` onto the first and second
branches, this relation forces both coefficients into `𝔪` as soon as a third branch is
present, a contradiction.

## Main results

* `Stacks.Curves.isOrdinaryDoublePoint_of_isGorenstein` — **Stacks 0CDZ**: a multicross
  singularity of a Gorenstein scheme over an algebraically closed field is a node.

## Implementation notes

Only the Gorenstein property of the local ring at `x` and the multicross description of its
completion enter the proof, so the reducedness, finite-type and one-dimensionality hypotheses
carried by the source are omitted.

The two coordinate projections are defined on the maximal ideal rather than on `A`: a tuple
with vanishing constant coefficients may be truncated to a single branch and stay inside the
multicross ring, which is false for a general tuple.

## References

* [Stacks Project, Tag 0C1U](https://stacks.math.columbia.edu/tag/0C1U)
* [Stacks Project, Tag 0C1W](https://stacks.math.columbia.edu/tag/0C1W)
* [Stacks Project, Tag 0CDZ](https://stacks.math.columbia.edu/tag/0CDZ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory IsLocalRing

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Curves

/-! ### Gorensteinness passes to the completed local ring -/

/-- The completion of a Gorenstein Noetherian local ring at its maximal ideal is Gorenstein:
the completion map is flat and local, and its closed fibre is the residue field. -/
private theorem isGorensteinLocalRing_adicCompletion
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hA : Dualizing.IsGorensteinLocalRing A) :
    Dualizing.IsGorensteinLocalRing (AdicCompletion (maximalIdeal A) A) := by
  let B := AdicCompletion (maximalIdeal A) A
  let I := (maximalIdeal A).map (algebraMap A B)
  let : Nontrivial (B ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr
    (IsLocalRing.map_maximalIdeal_lt_top (algebraMap A B)).ne
  let : IsLocalHom (Ideal.Quotient.mk I) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  let : IsLocalRing (B ⧸ I) :=
    IsLocalRing.of_surjective _ Ideal.Quotient.mk_surjective
  have hres : Dualizing.IsGorensteinLocalRing (B ⧸ I) := by
    have heq : I = maximalIdeal B := by
      dsimp [I, B]
      exact (AdicCompletion.maximalIdeal_eq_map :
        maximalIdeal (AdicCompletion (maximalIdeal A) A) = _).symm
    let e : (B ⧸ I) ≃+* IsLocalRing.ResidueField B := Ideal.quotEquivOfEq heq
    have hBres : Dualizing.IsGorensteinLocalRing (IsLocalRing.ResidueField B) :=
      Dualizing.IsRegularLocalRing.isGorensteinLocalRing (IsLocalRing.ResidueField B)
    exact Dualizing.isGorensteinLocalRing_of_ringEquiv e hBres
  exact (Dualizing.isGorensteinLocalRing_iff_of_flat A B).mpr ⟨hA, hres⟩

/-- On a Gorenstein scheme, the multicross ring describing the completed local ring at a
multicross singularity is a Gorenstein local ring. -/
private theorem isGorensteinLocalRing_of_hasMulticrossCompletion
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    (x : X) (n : ℕ) (hX : IsGorenstein X) (hcomp : HasMulticrossCompletion k X x n) :
    ∃ (_ : IsNoetherianRing ↥(multicross k n)) (_ : IsLocalRing ↥(multicross k n)),
        Dualizing.IsGorensteinLocalRing ↥(multicross k n) := by
  let : IsLocallyNoetherian X := hX.toIsLocallyNoetherian
  let A := X.presheaf.stalk x
  let B := AdicCompletion (maximalIdeal A) A
  let kToStalk : k →+* A :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop ≫
      X.presheaf.germ ⊤ x trivial).hom
  let : Algebra k A := kToStalk.toAlgebra
  obtain ⟨e⟩ := (hasMulticrossCompletion_iff k X x n).mp hcomp
  let eR : B ≃+* ↥(multicross k n) := e.toRingEquiv
  let : IsNoetherianRing ↥(multicross k n) := isNoetherianRing_of_ringEquiv B eR
  let : IsLocalRing ↥(multicross k n) := eR.isLocalRing
  exact ⟨inferInstance, inferInstance, Dualizing.isGorensteinLocalRing_of_ringEquiv eR.symm
    (isGorensteinLocalRing_adicCompletion A (hX.isGorensteinLocalRing x))⟩

/-! ### Two elements of `Ext¹(κ, A)` over a Gorenstein local ring -/

/-- Shifting the index of a homology functor on a derived category. -/
private noncomputable def homologyShiftIso
    {C : Type u} [Category C] [Abelian C] [HasDerivedCategory C]
    (K : DerivedCategory C) (i n : ℤ) :
    ((DerivedCategory.homologyFunctor C i).obj (K⟦n⟧)) ≅
      ((DerivedCategory.homologyFunctor C (i + n)).obj K) := by
  rw [← DerivedCategory.shift_homologyFunctor C i,
    ← DerivedCategory.shift_homologyFunctor C (i + n)]
  exact ((DerivedCategory.homologyFunctor C 0).shiftIso n i (i + n) (by omega)).app K

/-- Over a Gorenstein Noetherian local ring, `Ext¹` from the residue field to the regular
module embeds into a one-dimensional vector space, so any two of its elements satisfy a
nontrivial linear relation with a coefficient outside the maximal ideal. -/
private theorem exists_relation_ext_of_isGorenstein
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hA : Dualizing.IsGorensteinLocalRing A)
    (z₀ z₁ : CategoryTheory.Abelian.Ext
      ((ModuleCat.restrictScalars (Ideal.Quotient.mk (maximalIdeal A))).obj
        (ModuleCat.of (A ⧸ maximalIdeal A) (ULift.{0} (A ⧸ maximalIdeal A))))
      (ModuleCat.of A A) 1) :
    ∃ a b : A, (a ∉ maximalIdeal A ∨ b ∉ maximalIdeal A) ∧ a • z₀ + b • z₁ = 0 := by
  let m := maximalIdeal A
  let f : A →+* A ⧸ m := Ideal.Quotient.mk m
  let : Algebra A (A ⧸ m) := f.toAlgebra
  let K : DerivedCategory (ModuleCat.{u} A) :=
    (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)
  let RF := Dualizing.derivedHom.{u, 0} f
  let α := (Dualizing.coextendScalarsToDerivedCategory f).totalRightDerivedUnit
    DerivedCategory.Qh (HomotopyCategory.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))
  let E := (Dualizing.derivedCoextendScalarsHomologyLinearEquivExt.{u, 0} f RF α).linearEquiv
    K 1
  obtain ⟨n, ⟨e⟩⟩ := Dualizing.derivedHom_residueField_iso_shift.{u, 0} K hA m
    (IsLocalRing.maximalIdeal.isMaximal A)
  let S : DerivedCategory (ModuleCat.{u} (A ⧸ m)) :=
    (DerivedCategory.singleFunctor (ModuleCat.{u} (A ⧸ m)) 0).obj
      ((ModuleCat.uliftFunctor.{0} (A ⧸ m)).obj (ModuleCat.of (A ⧸ m) (A ⧸ m)))
  let R := ModuleCat.restrictScalars f
  let eHA := R.mapIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} (A ⧸ m)) 1).mapIso e ≪≫
    homologyShiftIso S 1 n)
  let L := CategoryTheory.Abelian.Ext.homLinearEquiv (R := A)
    (X := R.obj (ModuleCat.of (A ⧸ m) (ULift.{0} (A ⧸ m))))
    (Y := ModuleCat.of A A) (n := 1)
  have hinj {N : ModuleCat A} (e' : R.obj ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} (A ⧸ m)) 1).obj (RF.obj K)) ≅ N) :
      Function.Injective (e'.hom.hom.comp (E.symm.toLinearMap.comp L.toLinearMap)) := fun x y hxy =>
    L.injective (E.symm.injective ((ConcreteCategory.bijective_of_isIso e'.hom).1 hxy))
  by_cases hn : 1 + n = 0
  · obtain rfl : n = -1 := by omega
    have eHA0 : R.obj ((DerivedCategory.homologyFunctor (ModuleCat.{u} (A ⧸ m)) 1).obj
        (RF.obj K)) ≅ R.obj ((DerivedCategory.homologyFunctor
          (ModuleCat.{u} (A ⧸ m)) 0).obj S) := by
      simpa using eHA
    let e₀A := R.mapIso ((DerivedCategory.singleFunctorCompHomologyFunctorIso
      (ModuleCat.{u} (A ⧸ m)) 0).app (ModuleCat.of (A ⧸ m) (ULift.{0} (A ⧸ m))))
    let T : CategoryTheory.Abelian.Ext
        (R.obj (ModuleCat.of (A ⧸ m) (ULift.{0} (A ⧸ m)))) (ModuleCat.of A A) 1 →ₗ[A]
          ULift.{0} (A ⧸ m) :=
      (eHA0 ≪≫ e₀A).hom.hom.comp (E.symm.toLinearMap.comp L.toLinearMap)
    have hTinj : Function.Injective T := hinj _
    let p : ULift.{0} (A ⧸ m) := T z₀
    let q : ULift.{0} (A ⧸ m) := T z₁
    by_cases hpq : p.down = 0 ∧ q.down = 0
    · refine ⟨1, 0, ?_, ?_⟩
      · exact Or.inl (by simp)
      · have hp : p = 0 := by
          apply ULift.ext
          exact hpq.1
        have hzT : T z₀ = 0 := by simpa [p] using hp
        have hT : T z₀ = T 0 := by
          calc
            T z₀ = 0 := hzT
            _ = T 0 := by rw [map_zero]
        have hz : z₀ = 0 := hTinj hT
        simpa using hz
    · let aq := Classical.choose (Ideal.Quotient.mk_surjective q.down)
      let ap := Classical.choose (Ideal.Quotient.mk_surjective p.down)
      refine ⟨aq, -ap, ?_, ?_⟩
      · have hneq : p.down ≠ 0 ∨ q.down ≠ 0 := not_and_or.mp hpq
        rcases hneq with hp | hq
        · exact Or.inr (by
            intro hmem
            have hz : Ideal.Quotient.mk m (-ap) = 0 :=
              (Ideal.Quotient.eq_zero_iff_mem).2 hmem
            have hpz : -p.down = 0 := by
              calc
                -p.down = -(Ideal.Quotient.mk m ap) := by
                  rw [Classical.choose_spec (Ideal.Quotient.mk_surjective p.down)]
                _ = Ideal.Quotient.mk m (-ap) := by simp
                _ = 0 := hz
            exact hp (neg_eq_zero.mp hpz))
        · exact Or.inl (by
            intro hmem
            have hz : Ideal.Quotient.mk m aq = 0 :=
              (Ideal.Quotient.eq_zero_iff_mem).2 hmem
            have hqz : q.down = 0 := by
              calc
                q.down = Ideal.Quotient.mk m aq :=
                  (Classical.choose_spec (Ideal.Quotient.mk_surjective q.down)).symm
                _ = 0 := hz
            exact hq hqz)
      · have hval : aq • p + (-ap) • q = 0 := by
          apply ULift.ext
          simp only [neg_smul, ULift.add_down, ULift.smul_down, ULift.neg_down,
            ULift.zero_down]
          show f aq * p.down + -(f ap * q.down) = 0
          rw [Classical.choose_spec (Ideal.Quotient.mk_surjective q.down),
            Classical.choose_spec (Ideal.Quotient.mk_surjective p.down)]
          ring
        have hrel : T (aq • z₀ + -ap • z₁) = T 0 := by
          calc
            T (aq • z₀ + -ap • z₁) = aq • T z₀ + (-ap) • T z₁ := by simp
            _ = aq • p + (-ap) • q := by rfl
            _ = 0 := hval
            _ = T 0 := by rw [map_zero]
        exact hTinj hrel
  · refine ⟨1, 0, Or.inl ?_, ?_⟩
    · simp
    · have hzero : Subsingleton ((DerivedCategory.homologyFunctor
          (ModuleCat.{u} (A ⧸ m)) (1 + n)).obj S) := by
        by_cases hlt : 1 + n < 0
        · have : S.IsGE 0 := inferInstance
          exact ModuleCat.isZero_iff_subsingleton.mp
            (DerivedCategory.isZero_of_isGE S 0 (1 + n) hlt)
        · have hgt : 0 < 1 + n := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hn)
          have : S.IsLE 0 := inferInstance
          exact ModuleCat.isZero_iff_subsingleton.mp
            (DerivedCategory.isZero_of_isLE S 0 (1 + n) hgt)
      have hzeroA : Subsingleton ((ModuleCat.restrictScalars f).obj
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} (A ⧸ m)) (1 + n)).obj S)) := hzero
      let T : CategoryTheory.Abelian.Ext
          (R.obj (ModuleCat.of (A ⧸ m) (ULift.{0} (A ⧸ m)))) (ModuleCat.of A A) 1 →ₗ[A]
            (R.obj ((DerivedCategory.homologyFunctor (ModuleCat.{u} (A ⧸ m)) (1 + n)).obj S)) :=
        eHA.hom.hom.comp (E.symm.toLinearMap.comp L.toLinearMap)
      have hTinj : Function.Injective T := hinj _
      have hz₀ : T z₀ = 0 := hzeroA.elim (T z₀) 0
      have hz₀' : T z₀ = T 0 := by simpa [T, map_zero] using hz₀
      simpa using hTinj hz₀'

/-! ### The multicross ring with three or more branches is not Gorenstein -/

/-- The constant coefficient of the `i`-th branch, as a ring homomorphism on the multicross
ring. -/
private noncomputable def multicrossBranchConstantCoeff (k : Type u) [CommRing k] (n : ℕ)
    (i : Fin n) : ↥(multicross k n) →+* k :=
  PowerSeries.constantCoeff.comp ((Pi.evalRingHom _ i).comp (multicross k n).subtype)

/-- Every scalar is the constant coefficient of a branch of a multicross element. -/
private theorem multicrossBranchConstantCoeff_surjective (k : Type u) [CommRing k]
    (n : ℕ) (i : Fin n) : Function.Surjective (multicrossBranchConstantCoeff k n i) := by
  intro c
  let v : Fin n → PowerSeries k := fun _ => PowerSeries.C c
  have hv : v ∈ multicross k n := by
    rw [mem_multicross]
    intro j l
    simp [v]
  refine ⟨⟨v, hv⟩, ?_⟩
  simp [multicrossBranchConstantCoeff, v]

/-- The constant coefficient homomorphism reads off the constant coefficient of a branch. -/
private theorem multicrossBranchConstantCoeff_apply (k : Type u) [CommRing k] (n : ℕ)
    (i : Fin n) (z : ↥(multicross k n)) :
    multicrossBranchConstantCoeff k n i z = PowerSeries.constantCoeff (z.1 i) :=
  rfl

/-- The uniformizer of the `i`-th branch: the variable in that branch and zero elsewhere. -/
private noncomputable def multicrossBranchX (k : Type u) [CommRing k] (n : ℕ) (i : Fin n) :
    ↥(multicross k n) :=
  ⟨fun j => if j = i then PowerSeries.X else 0, by
    rw [mem_multicross]
    intro j l
    by_cases hj : j = i <;> by_cases hl : l = i <;> simp [hj, hl]⟩

/-- The `i`-th branch of the `i`-th uniformizer times an element. -/
private theorem multicrossBranchX_mul_val (k : Type u) [CommRing k] (n : ℕ) (i : Fin n)
    (z : ↥(multicross k n)) :
    (multicrossBranchX k n i * z).1 i = PowerSeries.X * z.1 i := by
  show (multicrossBranchX k n i).1 i * z.1 i = _
  simp [multicrossBranchX]

/-- The `i`-th branch of an element times the `i`-th uniformizer. -/
private theorem mul_multicrossBranchX_val (k : Type u) [CommRing k] (n : ℕ) (i : Fin n)
    (z : ↥(multicross k n)) :
    (z * multicrossBranchX k n i).1 i = z.1 i * PowerSeries.X := by
  show z.1 i * (multicrossBranchX k n i).1 i = _
  simp [multicrossBranchX]

/-- Multiplying by the `i`-th uniformizer moves the constant coefficient of the `i`-th branch
into degree one. -/
private theorem coeff_one_multicrossBranchX_mul (k : Type u) [CommRing k] (n : ℕ) (i : Fin n)
    (z : ↥(multicross k n)) :
    PowerSeries.coeff 1 ((multicrossBranchX k n i * z).1 i) =
      PowerSeries.constantCoeff (z.1 i) := by
  rw [multicrossBranchX_mul_val]
  simp

/-- The same computation with the factors in the other order. -/
private theorem coeff_one_mul_multicrossBranchX (k : Type u) [CommRing k] (n : ℕ) (i : Fin n)
    (z : ↥(multicross k n)) :
    PowerSeries.coeff 1 ((z * multicrossBranchX k n i).1 i) =
      PowerSeries.constantCoeff (z.1 i) := by
  rw [mul_multicrossBranchX_val]
  simp

/-- An element of the multicross ring is in the maximal ideal iff the constant coefficient of
one (equivalently every) branch vanishes. -/
private theorem mem_maximalIdeal_multicross_iff
    (k : Type u) [Field k] (n : ℕ) [IsLocalRing ↥(multicross k n)]
    (i₀ : Fin n) (z : ↥(multicross k n)) :
    z ∈ maximalIdeal ↥(multicross k n) ↔ PowerSeries.constantCoeff (z.1 i₀) = 0 := by
  rw [← IsLocalRing.ker_eq_maximalIdeal _ (multicrossBranchConstantCoeff_surjective k n i₀),
    RingHom.mem_ker, multicrossBranchConstantCoeff_apply]

/-- Every branch of an element of the maximal ideal has vanishing constant coefficient. -/
private theorem multicross_constantCoeff_eq_zero_of_mem_maximalIdeal
    (k : Type u) [Field k] (n : ℕ) [IsLocalRing ↥(multicross k n)]
    (i₀ i : Fin n) (z : ↥(multicross k n)) (hz : z ∈ maximalIdeal ↥(multicross k n)) :
    PowerSeries.constantCoeff (z.1 i) = 0 := by
  rw [z.2 i i₀]
  exact (mem_maximalIdeal_multicross_iff k n i₀ z).1 hz

/-- Truncating an element of the maximal ideal to its `i`-th branch stays in the multicross
ring, the other branches being zero and the `i`-th having no constant term. -/
private theorem multicross_supported_mem
    (k : Type u) [Field k] (n : ℕ) (i₀ i : Fin n) [IsLocalRing ↥(multicross k n)]
    (z : maximalIdeal ↥(multicross k n)) :
    (fun j => if j = i then z.1.1 j else 0) ∈ multicross k n := by
  rw [mem_multicross]
  intro j l
  have hconst (q : Fin n) : PowerSeries.constantCoeff (z.1.1 q) = 0 :=
    multicross_constantCoeff_eq_zero_of_mem_maximalIdeal k n i₀ q z.1 z.2
  by_cases hj : j = i
  · subst j
    by_cases hl : l = i
    · subst l
      rfl
    · simp [hl, hconst i]
  · by_cases hl : l = i
    · simp [hj, hl, hconst i]
    · simp [hj, hl]

/-- The projection of the maximal ideal onto its `i`-th branch, a map of modules over the
multicross ring. -/
private noncomputable def multicrossBranchProjection
    (k : Type u) [Field k] (n : ℕ) (i₀ i : Fin n) [IsLocalRing ↥(multicross k n)] :
    maximalIdeal ↥(multicross k n) →ₗ[↥(multicross k n)] ↥(multicross k n) := by
  refine
    { toFun := fun z => ⟨(fun j => if j = i then z.1.1 j else 0),
        multicross_supported_mem k n i₀ i z⟩
      map_add' := ?_
      map_smul' := ?_ }
  · intro z w
    apply Subtype.ext
    funext j
    by_cases hj : j = i <;> simp [hj]
  · intro a z
    apply Subtype.ext
    funext j
    by_cases hj : j = i <;> simp [hj]

/-- The multicross ring with at least three branches is not Gorenstein: the two coordinate
projections of the maximal ideal give two classes in `Ext¹(κ, A)` whose every relation has
both coefficients in the maximal ideal. -/
private theorem multicross_gorenstein_not_of_three_le
    (k : Type u) [Field k] (n : ℕ) (hn : 3 ≤ n)
    (hN : IsNoetherianRing ↥(multicross k n)) (hL : IsLocalRing ↥(multicross k n))
    (hG : Dualizing.IsGorensteinLocalRing ↥(multicross k n)) : False := by
  let A := ↥(multicross k n)
  let : IsNoetherianRing A := hN
  let : IsLocalRing A := hL
  let i₀ : Fin n := ⟨0, by omega⟩
  let i₁ : Fin n := ⟨1, by omega⟩
  let i₂ : Fin n := ⟨2, by omega⟩
  have h01 : i₀ ≠ i₁ := by simp [i₀, i₁]
  have h02 : i₀ ≠ i₂ := by simp [i₀, i₂]
  have h12 : i₁ ≠ i₂ := by simp [i₁, i₂]
  let m := maximalIdeal A
  let f : A →+* A ⧸ m := Ideal.Quotient.mk m
  let : Algebra A (A ⧸ m) := f.toAlgebra
  let R := ModuleCat.restrictScalars f
  let qmod : ModuleCat A := R.obj (ModuleCat.of (A ⧸ m) (ULift.{0} (A ⧸ m)))
  let g : A →ₗ[A] ↑qmod :=
    { toFun := fun z => ULift.up (Ideal.Quotient.mk m z)
      map_add' := by
        intro z w
        show ULift.up (Ideal.Quotient.mk m (z + w)) =
          ULift.up (Ideal.Quotient.mk m z + Ideal.Quotient.mk m w)
        exact congrArg ULift.up ((Ideal.Quotient.mk m).map_add z w)
      map_smul' := by
        intro r z
        show ULift.up (Ideal.Quotient.mk m (r * z)) =
          ULift.up (f r * Ideal.Quotient.mk m z)
        exact congrArg ULift.up ((Ideal.Quotient.mk m).map_mul r z) }
  let S : ShortComplex (ModuleCat A) := ModuleCat.shortComplexOfCompEqZero
    m.subtype g (by
      apply LinearMap.ext
      intro z
      have hz : Ideal.Quotient.mk m (m.subtype z) = 0 :=
        (Ideal.Quotient.eq_zero_iff_mem).2 z.property
      show ULift.up (Ideal.Quotient.mk m (m.subtype z)) = 0
      exact congrArg ULift.up hz)
  have hS : S.ShortExact := ModuleCat.shortComplex_shortExact S
    (by
      intro z
      constructor
      · intro hz
        have hz' : (Ideal.Quotient.mk m) z = 0 := by
          have h := congrArg ULift.down hz
          change (Ideal.Quotient.mk m) z = 0 at h
          exact h
        exact ⟨⟨z, (Ideal.Quotient.eq_zero_iff_mem).1 hz'⟩, rfl⟩
      · rintro ⟨⟨w, hw⟩, rfl⟩
        show ULift.up (Ideal.Quotient.mk m w) = 0
        apply ULift.ext
        exact (Ideal.Quotient.eq_zero_iff_mem).2 hw)
    (by intro z w h; exact Subtype.ext h)
    (by
      intro y
      obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective y.down
      refine ⟨z, ?_⟩
      show ULift.up (Ideal.Quotient.mk m z) = y
      apply ULift.ext
      exact hz)
  let e₀map := multicrossBranchProjection k n i₀ i₀
  let e₁map := multicrossBranchProjection k n i₀ i₁
  let e₀ : CategoryTheory.Abelian.Ext S.X₁ (ModuleCat.of A A) 0 :=
    CategoryTheory.Abelian.Ext.mk₀ (ModuleCat.ofHom e₀map)
  let e₁ : CategoryTheory.Abelian.Ext S.X₁ (ModuleCat.of A A) 0 :=
    CategoryTheory.Abelian.Ext.mk₀ (ModuleCat.ofHom e₁map)
  let z₀ := hS.extClass.comp e₀ (zero_add 1)
  let z₁ := hS.extClass.comp e₁ (zero_add 1)
  obtain ⟨a, b, hab, hrel⟩ := exists_relation_ext_of_isGorenstein A hG z₀ z₁
  let xcomb := a • e₀ + b • e₁
  have hxzero : hS.extClass.comp xcomb (zero_add 1) = 0 := by
    simpa [xcomb, z₀, z₁] using hrel
  obtain ⟨y, hy⟩ := CategoryTheory.Abelian.Ext.contravariant_sequence_exact₁
    hS (ModuleCat.of A A) xcomb (n₁ := 1) (by simp) hxzero
  let L0 := CategoryTheory.Abelian.Ext.linearEquiv₀ (R := A)
    (X := S.X₁) (Y := ModuleCat.of A A)
  let L02 := CategoryTheory.Abelian.Ext.linearEquiv₀ (R := A)
    (X := S.X₂) (Y := ModuleCat.of A A)
  let φ : S.X₂ ⟶ ModuleCat.of A A := L02 y
  have hy0 : CategoryTheory.Abelian.Ext.mk₀ φ = y :=
    CategoryTheory.Abelian.Ext.mk₀_linearEquiv₀_apply (R := A) y
  have hmk0 (v : S.X₁ ⟶ ModuleCat.of A A) :
      L0 (CategoryTheory.Abelian.Ext.mk₀ v) = v := by
    apply (CategoryTheory.Abelian.Ext.mk₀_bijective S.X₁ (ModuleCat.of A A)).1
    simp [L0]
  have hy' : (CategoryTheory.Abelian.Ext.mk₀ S.f).comp
      (CategoryTheory.Abelian.Ext.mk₀ φ) (zero_add 0) = xcomb := by
    rw [hy0]
    exact hy
  have hmap : φ.hom.comp m.subtype = a • e₀map + b • e₁map := by
    have h := congrArg L0 hy'
    rw [CategoryTheory.Abelian.Ext.mk₀_comp_mk₀] at h
    rw [hmk0] at h
    have hsum : L0 xcomb = a • ModuleCat.ofHom e₀map + b • ModuleCat.ofHom e₁map := by
      dsimp [xcomb, e₀, e₁]
      rw [L0.map_add, L0.map_smul, L0.map_smul, hmk0, hmk0]
    exact ModuleCat.hom_ext_iff.mp (h.trans hsum)
  let c : A := φ.hom 1
  have hφsmul (z : A) : φ.hom z = z • c := by
    calc
      φ.hom z = φ.hom (z • (1 : A)) := by simp
      _ = z • φ.hom 1 := φ.hom.map_smul z 1
      _ = z • c := rfl
  have htmem (i : Fin n) : multicrossBranchX k n i ∈ m := by
    refine (mem_maximalIdeal_multicross_iff k n i₀ _).2 ?_
    by_cases hi : i₀ = i <;> simp [multicrossBranchX, hi]
  let w₀ : m := ⟨multicrossBranchX k n i₀, htmem i₀⟩
  let w₁ : m := ⟨multicrossBranchX k n i₁, htmem i₁⟩
  let w₂ : m := ⟨multicrossBranchX k n i₂, htmem i₂⟩
  have he₀₀ : e₀map w₀ = multicrossBranchX k n i₀ := by
    apply Subtype.ext
    funext j
    by_cases hj : j = i₀ <;>
      simp [e₀map, multicrossBranchProjection, w₀, multicrossBranchX, hj]
  have he₁₀ : e₁map w₀ = 0 := by
    apply Subtype.ext
    funext j
    by_cases hj : j = i₁ <;>
      simp [e₁map, multicrossBranchProjection, w₀, multicrossBranchX, hj, h01.symm]
  have he₀₂ : e₀map w₂ = 0 := by
    apply Subtype.ext
    funext j
    by_cases hj : j = i₀ <;>
      simp [e₀map, multicrossBranchProjection, w₂, multicrossBranchX, hj, h02]
  have he₁₂ : e₁map w₂ = 0 := by
    apply Subtype.ext
    funext j
    by_cases hj : j = i₁ <;>
      simp [e₁map, multicrossBranchProjection, w₂, multicrossBranchX, hj, h12]
  have hval₂ : 0 = φ.hom (multicrossBranchX k n i₂) := by
    have h := LinearMap.congr_fun hmap w₂
    simpa [LinearMap.comp_apply, w₂, he₀₂, he₁₂, smul_eq_mul] using h.symm
  have hval₂' : (0 : A) = multicrossBranchX k n i₂ * c := by
    simpa [smul_eq_mul] using hval₂.trans (hφsmul (multicrossBranchX k n i₂))
  have hc₂ : PowerSeries.constantCoeff (c.1 i₂) = 0 := by
    rw [← coeff_one_multicrossBranchX_mul k n i₂ c, ← hval₂']
    simp
  have hc : c ∈ m := by
    refine (mem_maximalIdeal_multicross_iff k n i₀ _).2 ?_
    rw [c.2 i₀ i₂]
    exact hc₂
  have hmemX (i : Fin n) (x : A)
      (hx : x * multicrossBranchX k n i = φ.hom (multicrossBranchX k n i)) : x ∈ m := by
    have h := congrArg (fun q : A => PowerSeries.coeff 1 (q.1 i))
      (hx.trans ((hφsmul _).trans (smul_eq_mul _ _)))
    rw [coeff_one_mul_multicrossBranchX, coeff_one_multicrossBranchX_mul] at h
    refine (mem_maximalIdeal_multicross_iff k n i _).2 ?_
    rw [h]
    exact multicross_constantCoeff_eq_zero_of_mem_maximalIdeal k n i₀ i c hc
  have ha : a ∈ m := by
    refine hmemX i₀ a ?_
    have h := LinearMap.congr_fun hmap w₀
    simpa [LinearMap.comp_apply, w₀, he₀₀, he₁₀, smul_eq_mul] using h.symm
  have hb : b ∈ m := by
    refine hmemX i₁ b ?_
    have h := LinearMap.congr_fun hmap w₁
    have he₀₁ : e₀map w₁ = 0 := by
      apply Subtype.ext
      funext j
      by_cases hj : j = i₀ <;>
        simp [e₀map, multicrossBranchProjection, w₁, multicrossBranchX, hj, h01]
    have he₁₁ : e₁map w₁ = multicrossBranchX k n i₁ := by
      apply Subtype.ext
      funext j
      by_cases hj : j = i₁ <;>
        simp [e₁map, multicrossBranchProjection, w₁, multicrossBranchX, hj]
    simpa [LinearMap.comp_apply, w₁, he₀₁, he₁₁, smul_eq_mul, add_comm] using h.symm
  rcases hab with ha' | hb' <;> contradiction

/-! ### Gorenstein multicross singularities are nodes -/

/-- **Stacks 0CDZ.** A multicross singularity of a Gorenstein scheme over an algebraically
closed field is a node. -/
@[stacks 0CDZ]
theorem isOrdinaryDoublePoint_of_isGorenstein (k : Type u) [Field k] [IsAlgClosed k]
    (X : Scheme.{u}) [X.Over (Spec (.of k))] [IsGorenstein X] (x : X)
    (hx : IsMulticrossSingularity k X x) :
    IsOrdinaryDoublePoint k X x := by
  obtain ⟨n, hn, hcomp⟩ := hx.exists_hasMulticrossCompletion
  obtain ⟨hN, hL, hG⟩ :=
    isGorensteinLocalRing_of_hasMulticrossCompletion k X x n inferInstance hcomp
  obtain rfl : n = 2 := by
    by_contra hne
    exact multicross_gorenstein_not_of_three_le k n (by omega) hN hL hG
  exact ⟨hx.1, hcomp⟩

end Stacks.Curves

end
