module

public import StacksFrontier.AlgebraicGeometry.Divisors.DivisorPicardClass
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.CodimensionOne
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.UFDExtension
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierStalk.VanishingIdealStalk
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.CanonicalSectionOrder
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.FirstChernClass
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.GenericPoint
public import StacksFrontier.AlgebraicGeometry.UnitsNormalProper.Hartogs

/-!
# Surjectivity of the first Chern class over factorial local rings

Let `X` be a locally Noetherian integral scheme whose local rings are unique factorization
domains. Every Weil divisor on `X` is then the divisor of an invertible sheaf, so the first Chern
class `Pic(X) → Cl(X)` is surjective. This is the implication from condition (1) to the
surjectivity half of condition (2) in [Stacks, Tag 0BE9].

## Main definitions

* `AlgebraicGeometry.positiveWeilIdeal`: the ideal sheaf of the positive part of a Weil divisor.
* `AlgebraicGeometry.positiveWeilDivisor`: the positive part of a Weil divisor.

## Main results

* `AlgebraicGeometry.positiveWeilIdeal_isEffectiveCartierDivisor`: the ideal sheaf of the positive
  part is an effective Cartier divisor.
* `AlgebraicGeometry.weilDivisorClassOfInvertibleSheaf_positiveWeilIdeal`: the Weil divisor class
  of the invertible sheaf of that effective Cartier divisor is the class of the positive part.
* `AlgebraicGeometry.picardToWeilDivisorClassGroup_surjective`: the first Chern class is
  surjective when the local rings of `X` are unique factorization domains.

## References

* [Stacks Project, Tag 0BE9](https://stacks.math.columbia.edu/tag/0BE9)
* [Stacks Project, Tag 0AGA](https://stacks.math.columbia.edu/tag/0AGA)
* [Stacks Project, Tag 0AG8](https://stacks.math.columbia.edu/tag/0AG8)
* [Stacks Project, Tag 01WX](https://stacks.math.columbia.edu/tag/01WX)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Order TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-! ### The ideal sheaf of the positive part of a Weil divisor -/

/-- Only finitely many prime divisors with a nonzero coefficient in a Weil divisor `D` meet a
given affine open. -/
theorem finite_primeDivisors_meeting_affine (D : WeilDivisor X) (U : X.affineOpens) :
    {Z : PrimeDivisor X | D.val Z ≠ 0 ∧ (Z.support ∩ (U.1 : Set X)).Nonempty}.Finite := by
  classical
  have hloc : LocallyFinite (fun Z : PrimeDivisor X => if D.val Z = 0 then ∅ else Z.support) :=
    (mem_weilDivisor_iff D.val).mp D.property
  refine (hloc.finite_nonempty_inter_compact U.2.isCompact).subset fun Z hZ => ?_
  simp only [Set.mem_ofPred_eq] at hZ ⊢
  rw [ite_eq_right hZ.1]
  exact hZ.2

/-- An ideal sheaf whose support misses an affine open is the unit ideal there. -/
theorem ideal_eq_top_of_supportSet_inter_not_nonempty (I : X.IdealSheafData) (U : X.affineOpens)
    (h : ¬ (I.supportSet ∩ (U.1 : Set X)).Nonempty) : I.ideal U = ⊤ := by
  refine PrimeSpectrum.zeroLocus_empty_iff_eq_top.mp (Set.eq_empty_iff_forall_notMem.mpr ?_)
  intro y hy
  have hy' : U.2.fromSpec.base y ∈ X.zeroLocus (U := U.1) (I.ideal U) ∩ (U.1 : Set X) := by
    rw [← U.2.fromSpec_image_zeroLocus]
    exact ⟨y, hy, rfl⟩
  exact h ⟨_, I.zeroLocus_inter_subset_supportSet U hy', hy'.2⟩

/-- A power of the ideal of an ideal sheaf whose support misses an affine open is the unit ideal
there. -/
theorem ideal_pow_eq_one_of_supportSet_inter_not_nonempty (I : X.IdealSheafData)
    (U : X.affineOpens) (h : ¬ (I.supportSet ∩ (U.1 : Set X)).Nonempty) (n : ℕ) :
    I.ideal U ^ n = 1 := by
  rw [ideal_eq_top_of_supportSet_inter_not_nonempty I U h, Ideal.top_pow, Ideal.one_eq_top]

/-- The ideal sheaf of the positive part of a Weil divisor `D`: on an affine open `U` it is the
product of the `D_Z`-th powers of the ideals of the finitely many prime divisors `Z` with
`D_Z ≠ 0` meeting `U`. -/
def positiveWeilIdeal (D : WeilDivisor X) : X.IdealSheafData where
  ideal U := ∏ Z ∈ (finite_primeDivisors_meeting_affine D U).toFinset,
    Z.idealSheaf.ideal U ^ (D.val Z).toNat
  map_ideal_basicOpen U f := by
    classical
    have hsub : (finite_primeDivisors_meeting_affine D (X.affineBasicOpen f)).toFinset ⊆
        (finite_primeDivisors_meeting_affine D U).toFinset := by
      intro Z hZ
      simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hZ ⊢
      exact ⟨hZ.1, hZ.2.mono (Set.inter_subset_inter_right _ (X.basicOpen_le f))⟩
    rw [show Ideal.map (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom
          (∏ Z ∈ (finite_primeDivisors_meeting_affine D U).toFinset,
            Z.idealSheaf.ideal U ^ (D.val Z).toNat) =
        ∏ Z ∈ (finite_primeDivisors_meeting_affine D U).toFinset,
          (Z.idealSheaf.ideal U ^ (D.val Z).toNat).map
            (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom from
      map_prod (Ideal.mapHom _) _ _]
    simp_rw [Ideal.map_pow, Scheme.IdealSheafData.map_ideal_basicOpen]
    refine (Finset.prod_subset hsub ?_).symm
    intro Z hZU hZV
    have hne : D.val Z ≠ 0 := ((Set.Finite.mem_toFinset _).mp hZU).1
    have hd : ¬ ((Z.idealSheaf.supportSet) ∩ ((X.affineBasicOpen f).1 : Set X)).Nonempty := by
      intro hd
      exact hZV ((Set.Finite.mem_toFinset _).mpr ⟨hne, hd⟩)
    exact ideal_pow_eq_one_of_supportSet_inter_not_nonempty Z.idealSheaf (X.affineBasicOpen f)
      hd _

/-- On an affine open `U`, the ideal of `positiveWeilIdeal D` is the product over the prime
divisors `Z` meeting `U` with nonzero coefficient of `Z.idealSheaf.ideal U ^ (D.val Z).toNat`. -/
@[simp]
theorem positiveWeilIdeal_ideal (D : WeilDivisor X) (U : X.affineOpens) :
    (positiveWeilIdeal D).ideal U =
      ∏ Z ∈ (finite_primeDivisors_meeting_affine D U).toFinset,
        Z.idealSheaf.ideal U ^ (D.val Z).toNat :=
  rfl

/-- The component of a finite product of ideal sheaves is the product of the components. -/
theorem ideal_finsetProd {ι : Type*} (T : Finset ι) (I : ι → X.IdealSheafData)
    (U : X.affineOpens) : (∏ i ∈ T, I i).ideal U = ∏ i ∈ T, (I i).ideal U := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | @insert i T hi ih =>
    simp only [Finset.prod_insert hi, Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, ih]

/-- A finite product of powers of effective Cartier divisors is an effective Cartier divisor. -/
theorem isEffectiveCartierDivisor_finsetProd_pow {ι : Type*} (T : Finset ι)
    (I : ι → X.IdealSheafData) (n : ι → ℕ)
    (hI : ∀ i ∈ T, Stacks.Divisors.IsEffectiveCartierDivisor (I i)) :
    Stacks.Divisors.IsEffectiveCartierDivisor (∏ i ∈ T, I i ^ n i) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    simpa only [Finset.prod_empty, Scheme.IdealSheafData.one_eq_top] using
      Stacks.Divisors.IsEffectiveCartierDivisor.top (X := X)
  | @insert i T hi ih =>
    rw [Finset.prod_insert hi]
    have := hI i (Finset.mem_insert_self i T)
    have := ih fun j hj => hI j (Finset.mem_insert_of_mem hj)
    exact Stacks.Divisors.IsEffectiveCartierDivisor.mul _ _

variable [IsLocallyNoetherian X]

/-- When the local rings of `X` are unique factorization domains, the ideal sheaf of every prime
divisor is an effective Cartier divisor. -/
theorem PrimeDivisor.isEffectiveCartierDivisor_idealSheaf
    (hX : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) (Z : PrimeDivisor X) :
    Stacks.Divisors.IsEffectiveCartierDivisor Z.idealSheaf := by
  have := Z.integral
  exact isEffectiveCartierDivisor_of_codimension_one_of_uniqueFactorizationMonoid Z.idealSheaf
    Z.codimension_one fun x _ => hX x

/-- When the local rings of `X` are unique factorization domains, for every affine open `U` there
is an effective Cartier divisor whose ideal on `U` is that of `positiveWeilIdeal D`. -/
theorem exists_isEffectiveCartierDivisor_ideal_eq
    (hX : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) (D : WeilDivisor X)
    (U : X.affineOpens) :
    ∃ J : X.IdealSheafData, Stacks.Divisors.IsEffectiveCartierDivisor J ∧
      (positiveWeilIdeal D).ideal U = J.ideal U := by
  classical
  refine ⟨∏ Z ∈ (finite_primeDivisors_meeting_affine D U).toFinset,
      Z.idealSheaf ^ (D.val Z).toNat,
    isEffectiveCartierDivisor_finsetProd_pow _ _ _
      (fun Z _ => PrimeDivisor.isEffectiveCartierDivisor_idealSheaf hX Z), ?_⟩
  rw [ideal_finsetProd, positiveWeilIdeal_ideal]
  exact Finset.prod_congr rfl fun Z _ => rfl

/-- When the local rings of `X` are unique factorization domains, the ideal sheaf
`positiveWeilIdeal D` of the positive part of a Weil divisor is an effective Cartier divisor. -/
theorem positiveWeilIdeal_isEffectiveCartierDivisor
    (hX : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) (D : WeilDivisor X) :
    Stacks.Divisors.IsEffectiveCartierDivisor (positiveWeilIdeal D) := by
  refine isEffectiveCartierDivisor_of_stalk_regular_principal _ fun x _ => ?_
  obtain ⟨W, hW, hxW, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) trivial
  obtain ⟨J, hJ, hEq⟩ := exists_isEffectiveCartierDivisor_ideal_eq hX D ⟨W, hW⟩
  obtain ⟨f, hf, hfspan⟩ := exists_isRegular_stalk_eq_span_of_isEffectiveCartierDivisor J hJ x
  refine ⟨f, hf, ?_⟩
  rw [IdealSheafData.stalk_eq_map_germ _ x ⟨W, hW⟩ hxW, hEq,
    ← IdealSheafData.stalk_eq_map_germ J x ⟨W, hW⟩ hxW, hfspan]

/-! ### The stalk of the positive part at the generic point of a prime divisor -/

omit [IsLocallyNoetherian X] in
/-- A prime divisor whose support contains the generic point of a prime divisor `Z` is `Z`. -/
theorem PrimeDivisor.eq_of_genericPoint_mem_support {Z W : PrimeDivisor X}
    (h : Z.genericPoint ∈ W.support) : Z = W := by
  have hle : Z.genericPoint ≤ W.genericPoint := by
    rw [Scheme.le_iff_specializes, specializes_iff_mem_closure, ← W.support_eq_closure]
    exact h
  by_contra hne
  have hgp : Z.genericPoint ≠ W.genericPoint := fun hEq =>
    hne (PrimeDivisor.genericPoint_injective hEq)
  have hnot : ¬ W.genericPoint ≤ Z.genericPoint := fun hge =>
    hgp ((Scheme.le_iff_specializes.mp hge).antisymm (Scheme.le_iff_specializes.mp hle)).eq
  have hcoh := Order.coheight_add_one_le (lt_of_le_not_ge hle hnot)
  rw [PrimeDivisor.coheight_genericPoint, PrimeDivisor.coheight_genericPoint] at hcoh
  norm_num at hcoh

omit [IsLocallyNoetherian X] in
/-- The ideal a prime divisor induces in the local ring at its generic point is the maximal
ideal. -/
theorem PrimeDivisor.stalk_idealSheaf_genericPoint (Z : PrimeDivisor X) :
    IdealSheafData.stalk Z.idealSheaf Z.genericPoint =
      IsLocalRing.maximalIdeal (X.presheaf.stalk Z.genericPoint) := by
  have := Z.integral
  rw [show Z.idealSheaf = Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({Z.genericPoint} : Set X)) from
    (Stacks.Chow.integralComponentAt_genericPointOf Z.idealSheaf Z.integral).symm]
  exact Stacks.Divisors.stalk_vanishingIdeal_closure_singleton Z.genericPoint

omit [IsLocallyNoetherian X] in
/-- The ideal an ideal sheaf induces at a point outside its support is the unit ideal. -/
theorem IdealSheafData.stalk_eq_top_of_notMem_support (I : X.IdealSheafData) {x : X}
    (hx : x ∉ I.support) : IdealSheafData.stalk I x = ⊤ :=
  (IdealSheafData.stalk_eq_top_iff_notMem_support I x).mpr hx

omit [IsLocallyNoetherian X] in
/-- The ideal that `positiveWeilIdeal D` induces in the local ring at the generic point of a prime
divisor `Z` is the `D_Z`-th power of the maximal ideal. -/
theorem positiveWeilIdeal_stalk_genericPoint (D : WeilDivisor X) (Z : PrimeDivisor X) :
    IdealSheafData.stalk (positiveWeilIdeal D) Z.genericPoint =
      IsLocalRing.maximalIdeal (X.presheaf.stalk Z.genericPoint) ^ (D.val Z).toNat := by
  classical
  obtain ⟨W, hW, hxW, -⟩ :=
    exists_isAffineOpen_mem_and_subset (U := ⊤) (x := Z.genericPoint) trivial
  have hother : ∀ V ∈ (finite_primeDivisors_meeting_affine D ⟨W, hW⟩).toFinset, V ≠ Z →
      IdealSheafData.stalk V.idealSheaf Z.genericPoint ^ (D.val V).toNat = 1 := by
    intro V _ hV
    rw [IdealSheafData.stalk_eq_top_of_notMem_support V.idealSheaf
      (fun hmem => hV (PrimeDivisor.eq_of_genericPoint_mem_support hmem).symm)]
    simp
  rw [IdealSheafData.stalk_eq_map_germ _ Z.genericPoint ⟨W, hW⟩ hxW, positiveWeilIdeal_ideal,
    show Ideal.map (X.presheaf.germ (⟨W, hW⟩ : X.affineOpens).1 Z.genericPoint hxW).hom
        (∏ V ∈ (finite_primeDivisors_meeting_affine D ⟨W, hW⟩).toFinset,
          V.idealSheaf.ideal ⟨W, hW⟩ ^ (D.val V).toNat) =
        ∏ V ∈ (finite_primeDivisors_meeting_affine D ⟨W, hW⟩).toFinset,
          (V.idealSheaf.ideal ⟨W, hW⟩ ^ (D.val V).toNat).map
            (X.presheaf.germ (⟨W, hW⟩ : X.affineOpens).1 Z.genericPoint hxW).hom from
      map_prod (Ideal.mapHom _) _ _]
  have hterm : ∀ V : PrimeDivisor X,
      (V.idealSheaf.ideal ⟨W, hW⟩ ^ (D.val V).toNat).map
          (X.presheaf.germ (⟨W, hW⟩ : X.affineOpens).1 Z.genericPoint hxW).hom =
        IdealSheafData.stalk V.idealSheaf Z.genericPoint ^ (D.val V).toNat := by
    intro V
    rw [Ideal.map_pow, IdealSheafData.stalk_eq_map_germ V.idealSheaf Z.genericPoint ⟨W, hW⟩ hxW]
  simp only [hterm]
  by_cases hZ : D.val Z = 0
  · rw [hZ, Int.toNat_zero, pow_zero]
    refine Finset.prod_eq_one fun V hV => ?_
    by_cases he : V = Z
    · subst he
      rw [hZ, Int.toNat_zero, pow_zero]
    · exact hother V hV he
  · have hmemT : Z ∈ (finite_primeDivisors_meeting_affine D ⟨W, hW⟩).toFinset :=
      (Set.Finite.mem_toFinset _).mpr ⟨hZ, Z.genericPoint, by
        rw [PrimeDivisor.support_eq_closure]; exact subset_closure rfl, hxW⟩
    rw [Finset.prod_eq_single Z hother fun hnot => absurd hmemT hnot,
      PrimeDivisor.stalk_idealSheaf_genericPoint]

/-! ### The positive part of a Weil divisor -/

/-- The positive part of a Weil divisor: the coefficientwise `max` with zero. -/
def positiveWeilDivisor (D : WeilDivisor X) : WeilDivisor X := by
  classical
  refine ⟨fun Z => ((D.val Z).toNat : ℤ), ?_⟩
  rw [mem_weilDivisor_iff]
  refine ((mem_weilDivisor_iff D.val).mp D.property).subset fun Z => ?_
  by_cases h : D.val Z = 0
  · simp [h]
  · simp only [h, ite_false]
    split_ifs <;> simp

omit [IsLocallyNoetherian X] in
/-- The coefficient of `positiveWeilDivisor D` at a prime divisor `Z` is `(D.val Z).toNat`. -/
@[simp]
theorem positiveWeilDivisor_apply (D : WeilDivisor X) (Z : PrimeDivisor X) :
    (positiveWeilDivisor D).val Z = ((D.val Z).toNat : ℤ) :=
  rfl

omit [IsLocallyNoetherian X] in
/-- A Weil divisor is the difference of the positive parts of itself and of its negative. -/
theorem positiveWeilDivisor_sub_neg (D : WeilDivisor X) :
    positiveWeilDivisor D - positiveWeilDivisor (-D) = D := by
  refine Subtype.ext (funext fun Z => ?_)
  show ((D.val Z).toNat : ℤ) - (((-D).val Z).toNat : ℤ) = D.val Z
  show ((D.val Z).toNat : ℤ) - ((-D.val Z).toNat : ℤ) = D.val Z
  omega

/-! ### The Weil divisor class of the positive part -/

variable [IsIntegral X]

/-- In a discrete valuation ring, a generator of the `n`-th power of the maximal ideal has order
`n`. -/
theorem Ring.ord_eq_of_span_eq_maximalIdeal_pow {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (a : R) (n : ℕ)
    (h : Ideal.span {a} = IsLocalRing.maximalIdeal R ^ n) : Ring.ord R a = n := by
  rw [Ring.ord, h, IsDiscreteValuationRing.length_quotient_pow_maximalIdeal]

/-- At a codimension-one point whose local ring is a discrete valuation ring, the order of
vanishing of a generator of the `n`-th power of the maximal ideal is `n`. -/
theorem ord_algebraMap_eq_of_span_eq_maximalIdeal_pow (x : X) (hx : coheight x = 1)
    [IsDiscreteValuationRing (X.presheaf.stalk x)] (b : X.presheaf.stalk x) (n : ℕ)
    (hb : Ideal.span {b} = IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ n) :
    X.ord (algebraMap (X.presheaf.stalk x) X.functionField b) x = n := by
  have hne : IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ n ≠ ⊥ := by
    by_cases hn : n = 0
    · simp [hn]
    · exact (Ideal.pow_eq_bot hn).not.mpr (IsDiscreteValuationRing.not_a_field _)
  have hb0 : b ≠ 0 := fun h => hne (by rw [← hb, h, Ideal.span_singleton_zero])
  refine (X.ord_eq_iff hx ((map_ne_zero_iff _
    (IsFractionRing.injective (X.presheaf.stalk x) X.functionField)).mpr hb0)).mpr ?_
  show Ring.ordFrac (X.presheaf.stalk x) _ = _
  rw [Ring.ordFrac_eq_ord _ hb0]
  exact Ring.ordMonoidWithZeroHom_eq_coe _ (mem_nonZeroDivisors_iff_ne_zero.mpr hb0)
    (Ring.ord_eq_of_span_eq_maximalIdeal_pow b n hb)

/-- When the local rings of `X` are unique factorization domains, the Weil divisor class of the
invertible sheaf `Stacks.Divisors.modulesInvertibleSheaf (positiveWeilIdeal D)` is the class of
`positiveWeilDivisor D`. -/
theorem weilDivisorClassOfInvertibleSheaf_positiveWeilIdeal
    (hX : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) (D : WeilDivisor X) :
    letI : Stacks.Divisors.IsEffectiveCartierDivisor (positiveWeilIdeal D) :=
      positiveWeilIdeal_isEffectiveCartierDivisor hX D
    weilDivisorClassOfInvertibleSheaf X
        (Stacks.Divisors.modulesInvertibleSheaf (positiveWeilIdeal D)) =
      (positiveWeilDivisor D : weilDivisorClassGroup X) := by
  have : Stacks.Divisors.IsEffectiveCartierDivisor (positiveWeilIdeal D) :=
    positiveWeilIdeal_isEffectiveCartierDivisor hX D
  have : IsNormal X :=
    { stalk_isDomain := fun _ => inferInstance
      stalk_normal := fun x => by have := hX x; infer_instance }
  refine weilDivisorClassOfInvertibleSheaf_eq_of_forall_ord (positiveWeilIdeal D) _
    fun Z c hc => ?_
  have : IsDiscreteValuationRing (X.presheaf.stalk Z.genericPoint) :=
    Stacks.AlgebraicGeometry.UnitsNormalProper.isDiscreteValuationRing_stalk
      (PrimeDivisor.coheight_genericPoint Z)
  rw [positiveWeilDivisor_apply]
  exact (ord_algebraMap_eq_of_span_eq_maximalIdeal_pow Z.genericPoint
    (PrimeDivisor.coheight_genericPoint Z) c (D.val Z).toNat
    (hc.symm.trans (positiveWeilIdeal_stalk_genericPoint D Z))).symm

attribute [local instance] schemePicardGroupAddCommGroup

/-- On a locally Noetherian integral scheme whose local rings are unique factorization domains,
the first Chern class `picardToWeilDivisorClassGroup X : Pic(X) → Cl(X)` is surjective. -/
theorem picardToWeilDivisorClassGroup_surjective
    (hX : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) :
    Function.Surjective (picardToWeilDivisorClassGroup X) := by
  intro c
  induction c using QuotientAddGroup.induction_on with
  | _ D =>
    have key : ∀ E : WeilDivisor X, ∃ c, picardToWeilDivisorClassGroup X c =
        (positiveWeilDivisor E : weilDivisorClassGroup X) := fun E => by
      have : Stacks.Divisors.IsEffectiveCartierDivisor (positiveWeilIdeal E) :=
        positiveWeilIdeal_isEffectiveCartierDivisor hX E
      have hinv : Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
          (Stacks.Divisors.modulesInvertibleSheaf (positiveWeilIdeal E)) :=
        Stacks.Divisors.isTensorInvertible_invertibleSheaf _
      refine ⟨Stacks.SheafOfModules.picardClass X.sheaf.obj X.ringCatSheaf.property _ hinv, ?_⟩
      exact (weilDivisorClassOfPicardClass_picardClass X _).trans
        (weilDivisorClassOfInvertibleSheaf_positiveWeilIdeal hX E)
    obtain ⟨c₁, h₁⟩ := key D
    obtain ⟨c₂, h₂⟩ := key (-D)
    refine ⟨c₁ - c₂, ?_⟩
    rw [map_sub, h₁, h₂, show ((positiveWeilDivisor D : WeilDivisor X) : weilDivisorClassGroup X) -
        ((positiveWeilDivisor (-D) : WeilDivisor X) : weilDivisorClassGroup X) =
        ((positiveWeilDivisor D - positiveWeilDivisor (-D) : WeilDivisor X) :
          weilDivisorClassGroup X) from rfl, positiveWeilDivisor_sub_neg]

end AlgebraicGeometry

end
