module

public import StacksFrontier.AlgebraicGeometry.Chow.GysinCartierIntersection.IntersectionCoefficient

/-!
# Gysin pullback of the fundamental cycle of a closed subscheme

The Gysin pullback `i^*[Z]_{k+1} = [D ∩ Z]_k` of the fundamental cycle of a closed subscheme
(Stacks 02TB, part (1)), between cycles and between classes.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

open TopologicalSpace

open scoped TensorProduct

universe v w

open CategoryTheory.Limits Opposite

attribute [local instance] Classical.propDecidable

/-- A point of the support of an ideal sheaf lifts to its closed subscheme. -/
private lemma exists_subschemeι_eq_of_mem_support {X : Scheme.{u}} (Z : X.IdealSheafData) {y : X}
    (hy : y ∈ (Z.support : Set X)) : ∃ y' : Z.subscheme, Z.subschemeι y' = y := by
  rwa [← Z.range_subschemeι] at hy

/-- The image of a point of the closed subscheme lies in the support of its ideal sheaf. -/
private lemma subschemeι_mem_support {X : Scheme.{u}} (Z : X.IdealSheafData) (y : Z.subscheme) :
    Z.subschemeι y ∈ (Z.support : Set X) := by
  rw [← Z.range_subschemeι]
  exact ⟨y, rfl⟩

/-- A point in the image of the inverse image subscheme maps into the support of the ideal sheaf. -/
private lemma map_mem_support_of_mem_range_comap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (I : Y.IdealSheafData) {x : X} (hx : x ∈ Set.range (I.comap f).subschemeι) :
    f x ∈ (I.support : Set Y) := by
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.support_comap] at hx
  exact hx

/-- The stalk of an ideal sheaf at the image of a point of its subscheme is the kernel of the
stalk map. -/
private lemma stalk_eq_ker_stalkMap_subschemeι {X : Scheme.{u}} (Z : X.IdealSheafData)
    (y : Z.subscheme) :
    IdealSheafData.stalk Z (Z.subschemeι y) = RingHom.ker (Z.subschemeι.stalkMap y).hom := by
  have h := stalk_ker_closedImmersion Z.subschemeι y
  rwa [Scheme.IdealSheafData.ker_subschemeι] at h

/-- Points of a closed subscheme of dimension at most `m` have relative dimension at most `m`. -/
private lemma relativeDimension_subschemeι_le (C : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (m : ℤ) (Z : X.IdealSheafData)
    (hZ : schemeDeltaDimension C (Z.subschemeι ≫ p) ≤ (m : EInt)) (y : Z.subscheme) :
    relativeDimension C.dimensionFunction p (Z.subschemeι y) ≤ m :=
  WithTop.coe_le_coe.mp (WithBot.coe_le_coe.mp
    ((relativeDimension_le_closedSubschemeDimension_at C p Z.subschemeι y).trans hZ))

/-- A point of the spectrum of a local ring, other than the closed point, maps to a point other
than the base point. -/
private lemma fromSpecStalk_ne_of_ne_closedPoint {X : Scheme.{u}} (z : X)
    {q : PrimeSpectrum (X.presheaf.stalk z)}
    (hq : q ≠ IsLocalRing.closedPoint (X.presheaf.stalk z)) :
    X.fromSpecStalk z q ≠ z := fun he =>
  hq (fromSpecStalk_injective z (he.trans
    (AlgebraicGeometry.Scheme.fromSpecStalk_closedPoint (x := z)).symm))

/- A point of a closed subscheme of dimension at most `k + 1` whose relative dimension is
`k + 1` is a generic point of an irreducible component. -/
private lemma isGenericPoint_component_of_top_relativeDimension
    (C : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (m : ℤ) (Z : X.IdealSheafData)
    (hZ : schemeDeltaDimension C (Z.subschemeι ≫ p) ≤ (m : EInt))
    (y : Z.subscheme)
    (hy : relativeDimension C.dimensionFunction p (Z.subschemeι y) = m) :
    closure ({y} : Set Z.subscheme) ∈ irreducibleComponents Z.subscheme := by
  refine ⟨isIrreducible_singleton.closure, ?_⟩
  intro V hV hsub
  have hyV : y ∈ V := hsub (subset_closure rfl)
  have hgen : IsGenericPoint hV.genericPoint (closure V) :=
    hV.isGenericPoint_genericPoint_closure
  have hspec : hV.genericPoint ⤳ y :=
    specializes_iff_mem_closure.mpr (hgen ▸ subset_closure hyV)
  have heq : hV.genericPoint = y := by
    by_contra hne
    have hspecX : Z.subschemeι hV.genericPoint ⤳ Z.subschemeι y :=
      hspec.map Z.subschemeι.continuous
    have hneX : Z.subschemeι hV.genericPoint ≠ Z.subschemeι y := fun h =>
      hne (Z.subschemeι.isEmbedding.injective h)
    have hlt := relativeDimension_lt_of_specializes C p hspecX hneX
    have hle' := relativeDimension_subschemeι_le C p m Z hZ hV.genericPoint
    rw [hy] at hlt
    omega
  intro v hv
  rw [← heq, hgen]
  exact subset_closure hv

/-- A point of top relative dimension in a closed subscheme carrying an effective Cartier
divisor avoids that divisor. -/
theorem not_mem_support_of_top_dimension_of_effectiveCartier
    (C : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ) (Z D : X.IdealSheafData)
    (hZ : schemeDeltaDimension C (Z.subschemeι ≫ p) ≤ ((k + 1 : ℤ) : EInt))
    (hDZ : Stacks.Divisors.IsEffectiveCartierDivisor
      (D.comap Z.subschemeι))
    (y : X) (hy : y ∈ (Z.support : Set X))
    (hdim : relativeDimension C.dimensionFunction p y = k + 1) :
    y ∉ (D.support : Set X) := by
  let : IsLocallyNoetherian Z.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (Z.subschemeι ≫ p)
  obtain ⟨y', hy'⟩ := exists_subschemeι_eq_of_mem_support Z hy
  have hcomp := isGenericPoint_component_of_top_relativeDimension C p (k + 1) Z hZ y'
    (by rw [hy']; exact hdim)
  have hξ : Z.subschemeι y' ∉ (D.support : Set X) :=
    genericPoint_not_mem_support_of_effectiveCartier_comap Z D hDZ ⟨y', hcomp⟩
  rwa [hy'] at hξ

/- The intersection of a closed subscheme of dimension at most `k + 1` with a divisor it
meets properly has dimension at most `k`. -/
private lemma schemeDeltaDimension_comap_le_of_avoid
    (C : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ) (Z D : X.IdealSheafData)
    (hZ : schemeDeltaDimension C (Z.subschemeι ≫ p) ≤ ((k + 1 : ℤ) : EInt))
    (havoid : ∀ y : X, y ∈ (Z.support : Set X) →
      relativeDimension C.dimensionFunction p y = k + 1 →
        y ∉ (D.support : Set X)) :
    schemeDeltaDimension C
      ((Z.comap D.subschemeι).subschemeι ≫ D.subschemeι ≫ p) ≤ (k : EInt) := by
  rw [schemeDeltaDimension_eq_iSup]
  refine iSup_le fun W => ?_
  let ξ := W.2.1.genericPoint
  have hmemD := subschemeι_mem_support D ((Z.comap D.subschemeι).subschemeι ξ)
  have hmemZ := map_mem_support_of_mem_range_comap D.subschemeι Z (⟨ξ, rfl⟩ : _ ∈ Set.range _)
  obtain ⟨w', hw'⟩ := exists_subschemeι_eq_of_mem_support Z hmemZ
  have hle' := relativeDimension_subschemeι_le C p (k + 1) Z hZ w'
  rw [hw'] at hle'
  have hne : relativeDimension C.dimensionFunction p
      (D.subschemeι ((Z.comap D.subschemeι).subschemeι ξ)) ≠ k + 1 := fun he =>
    havoid _ hmemZ he hmemD
  have hlt : relativeDimension C.dimensionFunction p
      (D.subschemeι ((Z.comap D.subschemeι).subschemeι ξ)) ≤ k := by omega
  change (relativeDimension C.dimensionFunction
    ((Z.comap D.subschemeι).subschemeι ≫ D.subschemeι ≫ p) ξ : EInt) ≤ _
  rw [relativeDimension_comp_closedImmersion C.dimensionFunction
      (Z.comap D.subschemeι).subschemeι (D.subschemeι ≫ p) ξ,
    relativeDimension_comp_closedImmersion C.dimensionFunction D.subschemeι p
      ((Z.comap D.subschemeι).subschemeι ξ)]
  exact WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr hlt)

/- At a generic point of a component of an effective Cartier divisor on a closed
subscheme, the local ring of the subscheme is one-dimensional. -/
private lemma ringKrullDim_quotient_stalk_eq_one {X : Scheme.{u}} (Z D : X.IdealSheafData)
    [IsLocallyNoetherian Z.subscheme]
    (hDZ : Stacks.Divisors.IsEffectiveCartierDivisor
      (D.comap Z.subschemeι))
    (ξ : genericPoints (D.comap Z.subschemeι).subscheme) (w : X)
    (hw : Z.subschemeι ((D.comap Z.subschemeι).subschemeι ξ.1) = w) :
    ringKrullDim (X.presheaf.stalk w ⧸ IdealSheafData.stalk Z w) = 1 := by
  subst hw
  have hsurj := Z.subschemeι.stalkMap_surjective ((D.comap Z.subschemeι).subschemeι ξ.1)
  rw [stalk_eq_ker_stalkMap_subschemeι Z,
    ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective hsurj)]
  exact AlgebraicGeometry.ringKrullDim_stalk_eq_one_of_isEffectiveCartierDivisor
    (X := Z.subscheme) (D.comap Z.subschemeι) hDZ ξ.1
    ⟨⟨closure ({ξ.1} : Set (D.comap Z.subschemeι).subscheme), ξ.2⟩, isGenericPoint_closure⟩

/- A local equation for an effective Cartier divisor is a nonzerodivisor on the closed
subscheme carrying it. -/
private lemma isSMulRegular_quotient_stalk {X : Scheme.{u}} (Z D : X.IdealSheafData)
    [IsLocallyNoetherian Z.subscheme]
    (hDZ : Stacks.Divisors.IsEffectiveCartierDivisor
      (D.comap Z.subschemeι))
    (ξ : genericPoints (D.comap Z.subschemeι).subscheme) (w : X)
    (hw : Z.subschemeι ((D.comap Z.subschemeι).subschemeι ξ.1) = w)
    (a : X.presheaf.stalk w)
    (ha : IdealSheafData.stalk D w = Ideal.span {a}) :
    IsSMulRegular (X.presheaf.stalk w ⧸ IdealSheafData.stalk Z w) a := by
  subst hw
  have hsurj := Z.subschemeι.stalkMap_surjective ((D.comap Z.subschemeι).subschemeι ξ.1)
  -- the stalk of the divisor on the subscheme is generated by the image of `a`
  have hstalkE : IdealSheafData.stalk (D.comap Z.subschemeι)
      ((D.comap Z.subschemeι).subschemeι ξ.1) =
      Ideal.span {(Z.subschemeι.stalkMap ((D.comap Z.subschemeι).subschemeι ξ.1)).hom a} := by
    rw [AlgebraicGeometry.idealStalk_comap_eq_map Z.subschemeι D
      ((D.comap Z.subschemeι).subschemeι ξ.1), ha, Ideal.map_span, Set.image_singleton]
  -- a local nonzerodivisor equation for the divisor
  have hmem : ((D.comap Z.subschemeι).subschemeι ξ.1) ∈ (D.comap Z.subschemeι).supportSet :=
    subschemeι_mem_support _ ξ.1
  obtain ⟨U, hz₁U, f, hf, hideal⟩ :=
    effectiveCartier_affine_generator (D.comap Z.subschemeι) hDZ
      ((D.comap Z.subschemeι).subschemeι ξ.1) hmem
  let : Algebra Γ(Z.subscheme, U.1)
      (Z.subscheme.presheaf.stalk ((D.comap Z.subschemeι).subschemeι ξ.1)) :=
    (Z.subscheme.presheaf.germ U.1 ((D.comap Z.subschemeι).subschemeι ξ.1) hz₁U).hom.toAlgebra
  have : IsLocalization.AtPrime
      (Z.subscheme.presheaf.stalk ((D.comap Z.subschemeι).subschemeι ξ.1))
      (U.2.primeIdealOf ⟨((D.comap Z.subschemeι).subschemeι ξ.1), hz₁U⟩).asIdeal :=
    U.2.isLocalization_stalk ⟨((D.comap Z.subschemeι).subschemeι ξ.1), hz₁U⟩
  have hfnzd : f ∈ nonZeroDivisors Γ(Z.subscheme, U.1) :=
    (isRegular_iff_mem_nonZeroDivisors (R := Γ(Z.subscheme, U.1)) (r := f)).mp hf
  have hgermnzd :
      (Z.subscheme.presheaf.germ U.1 ((D.comap Z.subschemeι).subschemeι ξ.1) hz₁U).hom f ∈
      nonZeroDivisors (Z.subscheme.presheaf.stalk ((D.comap Z.subschemeι).subschemeι ξ.1)) :=
    IsLocalization.nonZeroDivisors_le_comap
      (U.2.primeIdealOf ⟨((D.comap Z.subschemeι).subschemeι ξ.1), hz₁U⟩).asIdeal.primeCompl _ hfnzd
  have hspanf : IdealSheafData.stalk (D.comap Z.subschemeι)
      ((D.comap Z.subschemeι).subschemeι ξ.1) =
      Ideal.span
        {(Z.subscheme.presheaf.germ U.1 ((D.comap Z.subschemeι).subschemeι ξ.1) hz₁U).hom f} := by
    rw [AlgebraicGeometry.IdealSheafData.stalk_eq_map_germ (D.comap Z.subschemeι)
      ((D.comap Z.subschemeι).subschemeι ξ.1) U hz₁U,
      hideal, Ideal.map_span, Set.image_singleton]
  have hreg : IsSMulRegular (Z.subscheme.presheaf.stalk ((D.comap Z.subschemeι).subschemeι ξ.1))
      ((Z.subschemeι.stalkMap ((D.comap Z.subschemeι).subschemeι ξ.1)).hom a) :=
    isSMulRegular_self_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_span_eq_span (hstalkE.symm.trans hspanf) hgermnzd)
  rw [stalk_eq_ker_stalkMap_subschemeι Z]
  exact isSMulRegular_quotient_ker
    (Z.subschemeι.stalkMap ((D.comap Z.subschemeι).subschemeι ξ.1)).hom hsurj a hreg

/- The coefficient of the cycle of an inverse image closed subscheme at a point which is
the image of a generic point of a component: the colength in the local ring of the image
of the ideal. -/
private theorem closedSubschemeCycleCoeff_comap_eq_length
    (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (f : X ⟶ Y)
    (I : Y.IdealSheafData) (k : ℤ) (x : X)
    (hgeneric : ∃ ξ : genericPoints (I.comap f).subscheme,
      (I.comap f).subschemeι ξ.1 = x)
    (hdim : relativeDimension C.dimensionFunction sX x = k) :
    closedSubschemeCycleCoeff C sX (I.comap f).subschemeι k x =
      ((Module.length (X.presheaf.stalk x)
        (X.presheaf.stalk x ⧸
          Ideal.map (f.stalkMap x).hom
            (IdealSheafData.stalk I (f x)))).toNat : ℤ) := by
  classical
  have key : ∀ ξ : genericPoints (I.comap f).subscheme,
      (I.comap f).subschemeι ξ.1 = x →
      componentMultiplicity (I.comap f).subschemeι ξ =
        ((Module.length (X.presheaf.stalk x)
          (X.presheaf.stalk x ⧸
            Ideal.map (f.stalkMap x).hom
              (IdealSheafData.stalk I (f x)))).toNat : ℤ) := by
    intro ξ hξ
    rw [componentMultiplicity_comap_eq_length_quotient f, hξ]
  unfold closedSubschemeCycleCoeff
  split_ifs with h
  · exact key (Classical.choose h) (Classical.choose_spec h).1
  · exact False.elim (h ⟨Classical.choose hgeneric,
      Classical.choose_spec hgeneric, hdim⟩)

/- The same coefficient for the intersection with a divisor cut out by `a`, as a colength
in the local ring of the ambient scheme: the shape in which Stacks 02QG states
additivity. -/
private theorem intersectionCycleCoeff_comap_eq_length_quotient_sup
    (C : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p]
    (D Z : X.IdealSheafData) (k : ℤ) (x : D.subscheme)
    (a : X.presheaf.stalk (D.subschemeι x))
    (hker : RingHom.ker (D.subschemeι.stalkMap x).hom = Ideal.span {a})
    (hgeneric : ∃ ξ : genericPoints (Z.comap D.subschemeι).subscheme,
      (Z.comap D.subschemeι).subschemeι ξ.1 = x)
    (hdim : relativeDimension C.dimensionFunction
      (D.subschemeι ≫ p) x = k) :
    (cycleAssociatedToClosedSubscheme C (D.subschemeι ≫ p)
        (Z.comap D.subschemeι).subschemeι k).1 x =
      ((Module.length (X.presheaf.stalk (D.subschemeι x))
        (X.presheaf.stalk (D.subschemeι x) ⧸
          (Ideal.span {a} ⊔
            IdealSheafData.stalk Z (D.subschemeι x)))).toNat : ℤ) := by
  change closedSubschemeCycleCoeff C (D.subschemeι ≫ p)
    (Z.comap D.subschemeι).subschemeι k x = _
  rw [closedSubschemeCycleCoeff_comap_eq_length C (D.subschemeι ≫ p) D.subschemeι Z k x
    hgeneric hdim]
  apply congrArg (fun n : ℕ∞ => (n.toNat : ℤ))
  calc
    Module.length (D.subscheme.presheaf.stalk x)
          (D.subscheme.presheaf.stalk x ⧸
            Ideal.map (D.subschemeι.stalkMap x).hom
              (IdealSheafData.stalk Z (D.subschemeι x))) =
        Module.length (X.presheaf.stalk (D.subschemeι x))
          (X.presheaf.stalk (D.subschemeι x) ⧸
            (IdealSheafData.stalk Z (D.subschemeι x) ⊔
              RingHom.ker (D.subschemeι.stalkMap x).hom)) :=
      (length_quotient_sup_ker_eq_length_quotient_map
        (D.subschemeι.stalkMap x).hom
        (D.subschemeι.stalkMap_surjective x)
        (IdealSheafData.stalk Z (D.subschemeι x))).symm
    _ = Module.length (X.presheaf.stalk (D.subschemeι x))
          (X.presheaf.stalk (D.subschemeι x) ⧸
            (Ideal.span {a} ⊔
              IdealSheafData.stalk Z (D.subschemeι x))) := by
      rw [hker, sup_comm]

/- The coefficient of the cycle of a closed subscheme at a non-closed point of the fibre
of `Scheme.fromSpecStalk` at `z`: the length of the localization at the corresponding
prime of the quotient of the local ring at `z`. -/
private lemma closedSubschemeCycle_fromSpecStalk
    (C : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ) (Z : X.IdealSheafData)
    (hZ : schemeDeltaDimension C (Z.subschemeι ≫ p) ≤ ((k + 1 : ℤ) : EInt))
    (z : X) (hz : relativeDimension C.dimensionFunction p z = k)
    (q : PrimeSpectrum (X.presheaf.stalk z))
    (hq : q ∈ Module.support (X.presheaf.stalk z)
      (X.presheaf.stalk z ⧸ IdealSheafData.stalk Z z))
    (hqne : q ≠ IsLocalRing.closedPoint (X.presheaf.stalk z)) :
    (cycleAssociatedToClosedSubscheme C p Z.subschemeι (k + 1)).1
        (X.fromSpecStalk z q) =
      ((Module.length (Localization.AtPrime q.asIdeal)
        (LocalizedModule q.asIdeal.primeCompl
          (X.presheaf.stalk z ⧸ IdealSheafData.stalk Z z))).toNat : ℤ) := by
  classical
  have hysupp : X.fromSpecStalk z q ∈ (Z.support : Set X) :=
    (mem_support_fromSpecStalk_iff Z z q).mpr hq
  have hrel := relativeDimension_eq_succ_of_specializes_support C p k Z hZ hysupp
    (specializes_fromSpecStalk z q) (fromSpecStalk_ne_of_ne_closedPoint z hqne) hz
  obtain ⟨y, hy⟩ := exists_subschemeι_eq_of_mem_support Z hysupp
  have hcomp := isGenericPoint_component_of_top_relativeDimension C p (k + 1) Z hZ y
    (by rw [hy]; exact hrel)
  have hcoeff := cycleAssociatedToClosedSubscheme_apply C p Z.subschemeι (k + 1)
    ⟨y, hcomp⟩ (by rw [hy]; exact hrel)
  rw [hy] at hcoeff
  rw [hcoeff, componentMultiplicity_eq_length_quotient_ker, ← stalk_eq_ker_stalkMap_subschemeι Z y,
    hy,
    length_quotient_stalk_fromSpecStalk_eq_length_localized Z z q]

/- A nonzero coefficient of the cycle of a closed subscheme comes from a generic point of
a component of the expected dimension. -/
private lemma exists_genericPoint_of_closedSubschemeCycle_ne_zero
    (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (i : Y ⟶ X) [IsClosedImmersion i] (k : ℤ)
    (y : X) (h : (cycleAssociatedToClosedSubscheme C f i k).1 y ≠ 0) :
    ∃ ξ : genericPoints Y, i ξ.1 = y ∧
      relativeDimension C.dimensionFunction f y = k := by
  by_contra hcon
  exact h (cycleAssociatedToClosedSubscheme_apply_eq_zero C f i k y hcon)

/- The geometric sum computing the Gysin coefficient of the cycle of a closed subscheme at
`x`, reindexed over the minimal primes of the stalk of its ideal sheaf at the image of
`x`. The two indexings correspond under `Scheme.fromSpecStalk`. -/
private lemma gysin_sum_eq_sum_minimalPrimes_closedSubscheme
    (C : ChowSituation.{u}) {X : Scheme.{u}} [IsLocallyNoetherian X]
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ) (Z : X.IdealSheafData)
    (hZ : schemeDeltaDimension C (Z.subschemeι ≫ p) ≤ ((k + 1 : ℤ) : EInt))
    (D : X.IdealSheafData) (x : D.subscheme)
    (hδ : relativeDimension C.dimensionFunction (D.subschemeι ≫ p) x = k)
    (a : X.presheaf.stalk (D.subschemeι x))
    (hker : RingHom.ker (D.subschemeι.stalkMap x).hom = Ideal.span {a})
    (hqne : ∀ q : PrimeSpectrum (X.presheaf.stalk (D.subschemeι x)),
      Minimal (· ∈ Module.support (X.presheaf.stalk (D.subschemeι x))
        (X.presheaf.stalk (D.subschemeι x) ⧸
          IdealSheafData.stalk Z (D.subschemeι x))) q →
      q ≠ IsLocalRing.closedPoint (X.presheaf.stalk (D.subschemeι x)))
    (havoid : ∀ y : X, y ∈ (Z.support : Set X) →
      relativeDimension C.dimensionFunction p y = k + 1 →
      y ∉ (D.support : Set X)) :
    (∑ᶠ y : {y : X //
          (cycleAssociatedToClosedSubscheme C p Z.subschemeι (k + 1)).1 y ≠ 0},
        (cycleAssociatedToClosedSubscheme C p Z.subschemeι (k + 1)).1 y.1 *
          (cycleAssociatedToClosedSubscheme C (D.subschemeι ≫ p)
            (((reducedPointClosure y.1).comap D.subschemeι).subschemeι) k).1 x) =
      ∑ᶠ q ∈ {q : PrimeSpectrum (X.presheaf.stalk (D.subschemeι x)) |
          Minimal (· ∈ Module.support (X.presheaf.stalk (D.subschemeι x))
            (X.presheaf.stalk (D.subschemeι x) ⧸
              IdealSheafData.stalk Z (D.subschemeι x))) q},
        ((Module.length (X.presheaf.stalk (D.subschemeι x))
            ((X.presheaf.stalk (D.subschemeι x)) ⧸
              (Ideal.span {a} ⊔ q.asIdeal))).toNat : ℤ) *
          ((Module.length (Localization.AtPrime q.asIdeal)
            (LocalizedModule q.asIdeal.primeCompl
              (X.presheaf.stalk (D.subschemeι x) ⧸
                IdealSheafData.stalk Z (D.subschemeι x)))).toNat : ℤ) := by
  classical
  have hzrel : relativeDimension C.dimensionFunction p (D.subschemeι x) = k := by
    rw [← relativeDimension_comp_closedImmersion C.dimensionFunction D.subschemeι p x]
    exact hδ
  have hle : ∀ y : X, y ∈ (Z.support : Set X) →
      relativeDimension C.dimensionFunction p y ≤ k + 1 := by
    intro y hy
    obtain ⟨y', rfl⟩ := exists_subschemeι_eq_of_mem_support Z hy
    exact relativeDimension_subschemeι_le C p (k + 1) Z hZ y'
  have hsupp : ∀ q : PrimeSpectrum (X.presheaf.stalk (D.subschemeι x)),
      q ∈ Module.support (X.presheaf.stalk (D.subschemeι x))
        (X.presheaf.stalk (D.subschemeι x) ⧸
          IdealSheafData.stalk Z (D.subschemeι x)) →
      X.fromSpecStalk (D.subschemeι x) q ∈ (Z.support : Set X) := fun q hq =>
    (mem_support_fromSpecStalk_iff Z (D.subschemeι x) q).mpr hq
  have hrel : ∀ q : PrimeSpectrum (X.presheaf.stalk (D.subschemeι x)),
      q ∈ Module.support (X.presheaf.stalk (D.subschemeι x))
        (X.presheaf.stalk (D.subschemeι x) ⧸
          IdealSheafData.stalk Z (D.subschemeι x)) →
      q ≠ IsLocalRing.closedPoint (X.presheaf.stalk (D.subschemeι x)) →
      relativeDimension C.dimensionFunction p
        (X.fromSpecStalk (D.subschemeι x) q) = k + 1 := by
    intro q hq hqc
    exact relativeDimension_eq_succ_of_specializes_support C p k Z hZ (hsupp q hq)
      (specializes_fromSpecStalk _ q) (fromSpecStalk_ne_of_ne_closedPoint _ hqc) hzrel
  have hterm : ∀ q ∈ {q : PrimeSpectrum (X.presheaf.stalk (D.subschemeι x)) |
        Minimal (· ∈ Module.support (X.presheaf.stalk (D.subschemeι x))
          (X.presheaf.stalk (D.subschemeι x) ⧸
            IdealSheafData.stalk Z (D.subschemeι x))) q},
      (cycleAssociatedToClosedSubscheme C p Z.subschemeι (k + 1)).1
          (X.fromSpecStalk (D.subschemeι x) q) *
        (cycleAssociatedToClosedSubscheme C (D.subschemeι ≫ p)
          (((reducedPointClosure (X.fromSpecStalk (D.subschemeι x) q)).comap
            D.subschemeι).subschemeι) k).1 x =
      ((Module.length (X.presheaf.stalk (D.subschemeι x))
          ((X.presheaf.stalk (D.subschemeι x)) ⧸
            (Ideal.span {a} ⊔ q.asIdeal))).toNat : ℤ) *
        ((Module.length (Localization.AtPrime q.asIdeal)
          (LocalizedModule q.asIdeal.primeCompl
            (X.presheaf.stalk (D.subschemeι x) ⧸
              IdealSheafData.stalk Z (D.subschemeι x)))).toNat : ℤ) := by
    intro q hq
    have hgeneric := exists_genericPoint_comap_reducedPointClosure C p k D x
      (X.fromSpecStalk (D.subschemeι x) q) (specializes_fromSpecStalk _ q)
      (havoid _ (hsupp q hq.1) (hrel q hq.1 (hqne q hq))) (hrel q hq.1 (hqne q hq)) hδ
    rw [closedSubschemeCycle_fromSpecStalk C p k Z hZ (D.subschemeι x) hzrel q hq.1
        (hqne q hq),
      intersectionCycleCoeff_eq_length_quotient_sup C p D k x a hker q hgeneric hδ]
    exact mul_comm _ _
  have hinj : Set.InjOn (fun q : PrimeSpectrum (X.presheaf.stalk (D.subschemeι x)) =>
      X.fromSpecStalk (D.subschemeι x) q)
      {q : PrimeSpectrum (X.presheaf.stalk (D.subschemeι x)) |
        Minimal (· ∈ Module.support (X.presheaf.stalk (D.subschemeι x))
          (X.presheaf.stalk (D.subschemeι x) ⧸
            IdealSheafData.stalk Z (D.subschemeι x))) q} :=
    fun q _ q' _ h => fromSpecStalk_injective _ h
  have hP : ∀ y ∈ Function.support (fun y : X =>
        (cycleAssociatedToClosedSubscheme C p Z.subschemeι (k + 1)).1 y *
          (cycleAssociatedToClosedSubscheme C (D.subschemeι ≫ p)
            (((reducedPointClosure y).comap D.subschemeι).subschemeι) k).1 x),
      ((cycleAssociatedToClosedSubscheme C p Z.subschemeι (k + 1)).1 y ≠ 0 ↔
        y ∈ (fun q : PrimeSpectrum (X.presheaf.stalk (D.subschemeι x)) =>
            X.fromSpecStalk (D.subschemeι x) q) ''
          {q : PrimeSpectrum (X.presheaf.stalk (D.subschemeι x)) |
            Minimal (· ∈ Module.support (X.presheaf.stalk (D.subschemeι x))
              (X.presheaf.stalk (D.subschemeι x) ⧸
                IdealSheafData.stalk Z (D.subschemeι x))) q}) := by
    intro y hy
    have hy' : (cycleAssociatedToClosedSubscheme C p Z.subschemeι (k + 1)).1 y *
        (cycleAssociatedToClosedSubscheme C (D.subschemeι ≫ p)
          (((reducedPointClosure y).comap D.subschemeι).subschemeι) k).1 x ≠ 0 := hy
    have hα : (cycleAssociatedToClosedSubscheme C p Z.subschemeι (k + 1)).1 y ≠ 0 :=
      fun h => hy' (by rw [h, zero_mul])
    have hβ : (cycleAssociatedToClosedSubscheme C (D.subschemeι ≫ p)
        (((reducedPointClosure y).comap D.subschemeι).subschemeι) k).1 x ≠ 0 :=
      fun h => hy' (by rw [h, mul_zero])
    refine ⟨fun _ => ?_, fun _ => hα⟩
    obtain ⟨ζ, hζ, hyrel⟩ := exists_genericPoint_of_closedSubschemeCycle_ne_zero C p
      Z.subschemeι (k + 1) y hα
    have hysupp : y ∈ (Z.support : Set X) := hζ ▸ subschemeι_mem_support Z ζ.1
    have hxr := map_mem_support_of_mem_range_comap D.subschemeι (reducedPointClosure y)
      (closedSubscheme_cycle_nonzero_mem_support C (D.subschemeι ≫ p)
        (((reducedPointClosure y).comap D.subschemeι).subschemeι) k x hβ)
    have hclos : D.subschemeι x ∈ closure ({y} : Set X) := by
      rwa [reducedPointClosure_support] at hxr
    have hspec : y ⤳ D.subschemeι x := specializes_iff_mem_closure.mpr hclos
    have hyrange : y ∈ Set.range (X.fromSpecStalk (D.subschemeι x)) := by
      rw [Scheme.range_fromSpecStalk]
      exact hspec
    obtain ⟨q, hqy⟩ := hyrange
    refine ⟨q, ?_, hqy⟩
    have hqmem : q ∈ Module.support (X.presheaf.stalk (D.subschemeι x))
        (X.presheaf.stalk (D.subschemeι x) ⧸
          IdealSheafData.stalk Z (D.subschemeι x)) :=
      (mem_support_fromSpecStalk_iff Z (D.subschemeι x) q).mp (by rw [hqy]; exact hysupp)
    refine ⟨hqmem, ?_⟩
    intro q' hq' hle'
    by_cases hqq : q' = q
    · exact le_of_eq hqq.symm
    · exfalso
      have hspec' : X.fromSpecStalk (D.subschemeι x) q' ⤳
          X.fromSpecStalk (D.subschemeι x) q :=
        ((PrimeSpectrum.le_iff_specializes q' q).mp hle').map
          (X.fromSpecStalk (D.subschemeι x)).continuous
      have hne' : X.fromSpecStalk (D.subschemeι x) q' ≠
          X.fromSpecStalk (D.subschemeι x) q := fun h =>
        hqq (fromSpecStalk_injective _ h)
      have hlt := relativeDimension_lt_of_specializes C p hspec' hne'
      have hbound := hle _ (hsupp q' hq')
      rw [hqy, hyrel] at hlt
      omega
  exact (finsum_subtype_eq_finsum_mem_image _ _ _ _ hinj hP).trans
    (finsum_mem_congr rfl hterm)

/-- Intersecting a closed subscheme properly with a Cartier zero scheme computes its Gysin
cycle: the Gysin rule of `L` and `s`, extended coefficientwise, sends `[Z]_{k+1}` to the
fundamental cycle `[D ∩ Z]_k` of the scheme-theoretic intersection. -/
theorem gysinRule_extendCycleGroup_cycleAssociatedToClosedSubscheme
    (C : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)
    (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : L.sections) (Z : X.IdealSheafData)
    (hZ : schemeDeltaDimension C (Z.subschemeι ≫ p) ≤
      ((k + 1 : ℤ) : EInt))
    (hDZ : Stacks.Divisors.IsEffectiveCartierDivisor
      ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).comap Z.subschemeι)) :
    (gysinRule C p k L (s.eval (.op ⊤)) (firstChernComponentClass C p k L)).extendCycleGroup
        (cycleAssociatedToClosedSubscheme C p Z.subschemeι (k + 1)) =
      cycleAssociatedToClosedSubscheme C
        ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ p)
        ((Z.comap (Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι).subschemeι) k := by
  classical
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : IsLocallyNoetherian Z.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (Z.subschemeι ≫ p)
  have hZclosed : IsClosed (Z.support : Set X) := by
    rw [← Z.range_subschemeι]
    exact Z.subschemeι.isClosedEmbedding.isClosed_range
  have havoid : ∀ y : X, y ∈ (Z.support : Set X) →
      relativeDimension C.dimensionFunction p y = k + 1 →
      y ∉ (((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).support : Set X)) :=
    not_mem_support_of_top_dimension_of_effectiveCartier C p k Z
      (Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))) hZ hDZ
  have havoid' : ∀ y : X,
      (cycleAssociatedToClosedSubscheme C p Z.subschemeι (k + 1)).1 y ≠ 0 →
      ¬ (Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))) ≤ reducedPointClosure y := by
    intro y hy hle
    obtain ⟨ζ, hζ, hyrel⟩ := exists_genericPoint_of_closedSubschemeCycle_ne_zero C p
      Z.subschemeι (k + 1) y hy
    refine havoid y (hζ ▸ subschemeι_mem_support Z ζ.1) hyrel ?_
    apply Scheme.IdealSheafData.support_antitone hle
    change y ∈ ((reducedPointClosure y).support : Set X)
    rw [reducedPointClosure_support]
    exact subset_closure (Set.mem_singleton y)
  have hcoeff : ∀ x : (Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subscheme,
      ((gysinRule C p k L (s.eval (.op ⊤))
            (firstChernComponentClass C p k L)).extendCycleGroup
          (cycleAssociatedToClosedSubscheme C p Z.subschemeι (k + 1))).1 x =
        ∑ᶠ y : {y : X // (cycleAssociatedToClosedSubscheme C p Z.subschemeι (k + 1)).1 y ≠ 0},
          (cycleAssociatedToClosedSubscheme C p Z.subschemeι (k + 1)).1 y.1 *
            (cycleAssociatedToClosedSubscheme C
              ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ p)
              (((reducedPointClosure y.1).comap
                (Stacks.Divisors.zeroScheme X L
                  (s.eval (.op ⊤))).subschemeι).subschemeι) k).1 x := by
    intro x
    rw [(gysinRule C p k L (s.eval (.op ⊤))
      (firstChernComponentClass C p k L)).extendCycleGroup_apply_of_presentation
      (fun y : {y : X // (cycleAssociatedToClosedSubscheme C p Z.subschemeι (k + 1)).1 y ≠ 0} ↦
        reducedPointClosure y.1)
      (fun y ↦ isIntegral_reducedPointClosure y.1)
      (fun y ↦ by
        rw [reducedPointClosure_schemeDeltaDimension,
          cycle_dimension_at_support C p (k + 1)
            (cycleAssociatedToClosedSubscheme C p Z.subschemeι (k + 1)) y.1 y.2])
      (locallyFinite_reducedPointClosure_support
        (cycleAssociatedToClosedSubscheme C p Z.subschemeι (k + 1)).1)
      (fun y ↦ (cycleAssociatedToClosedSubscheme C p Z.subschemeι (k + 1)).1 y.1) _
      (cycle_eq_finsum_reducedPointClosure C p (k + 1)
        (cycleAssociatedToClosedSubscheme C p Z.subschemeι (k + 1))) x]
    refine finsum_congr fun y ↦ ?_
    congr 2
    exact congrArg Subtype.val (gysinComponentCycle_of_not_le C p k L (s.eval (.op ⊤))
      (firstChernComponentClass C p k L) (reducedPointClosure y.1)
      (isIntegral_reducedPointClosure y.1) _ (havoid' y.1 y.2))
  apply Subtype.ext
  apply DFunLike.ext
  intro x
  rw [hcoeff]
  by_cases hgen : ∃ ξ : genericPoints
      (Z.comap (Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι).subscheme,
      (Z.comap (Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι).subschemeι ξ.1 = x ∧
        relativeDimension C.dimensionFunction
          ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ p) x = k
  · obtain ⟨ξ, hξ, hdim⟩ := hgen
    have hzD : (Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι x ∈
        (Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).support :=
      subschemeι_mem_support _ x
    obtain ⟨a, hker, haMax⟩ : ∃ a : X.presheaf.stalk
        ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι x),
        RingHom.ker ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι.stalkMap x).hom =
          Ideal.span {a} ∧
          a ∈ IsLocalRing.maximalIdeal
            (X.presheaf.stalk ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι
                x)) := by
      obtain ⟨U, eU, -, hzU, -⟩ := exists_affine_frame_subset X L
          ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι x) ⊤ trivial
      exact ⟨_, ker_zeroScheme_stalkMap_of_frame X L s U eU x hzU,
        frame_coordinate_mem_maximalIdeal X L s U eU
          ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι x) hzU hzD⟩
    have hstalkD : IdealSheafData.stalk (Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤)))
        ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι x) = Ideal.span {a} := by
      rw [stalk_eq_ker_stalkMap_subschemeι, hker]
    obtain ⟨η, hη⟩ := exists_genericPoint_comap_symm Z
        (Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))) ξ.1 ξ.2
    have hηeq : Z.subschemeι
        (((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).comap Z.subschemeι).subschemeι η.1) =
        (Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι x := by
      rw [hη, hξ]
    have hdim1 := ringKrullDim_quotient_stalk_eq_one Z
        (Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))) hDZ η
        ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι x) hηeq
    have hreg := isSMulRegular_quotient_stalk Z (Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤)))
        hDZ η ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι x) hηeq a hstalkD
    have hM : Module.supportDim
        (X.presheaf.stalk ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι x))
        (X.presheaf.stalk ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι x) ⧸
          IdealSheafData.stalk Z ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι x)) =
            1 := by
      rw [Module.supportDim_quotient_eq_ringKrullDim, hdim1]
    have hQ : IsFiniteLength
        (X.presheaf.stalk ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι x))
        (QuotSMulTop a
          (X.presheaf.stalk ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι x) ⧸
          IdealSheafData.stalk Z
            ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι x))) :=
      finite_length_of_supportDim_le_zero
        (le_of_eq (supportDim_quotSMulTop_eq_zero_of_dim_one hM hreg haMax))
    have hsum := length_quotSMulTop_eq_sum_of_regular_of_supportDim_eq_one a hreg haMax hM
    have hlocalInt :
        ((Module.length (X.presheaf.stalk
          ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι x))
          (QuotSMulTop a
            (X.presheaf.stalk ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι x) ⧸
            IdealSheafData.stalk Z
              ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι x)))).toNat : ℤ) =
        ∑ᶠ q ∈
          {q : PrimeSpectrum
            (X.presheaf.stalk ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι x)) |
            Minimal (· ∈ Module.support
              (X.presheaf.stalk ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι x))
              (X.presheaf.stalk ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι x) ⧸
                IdealSheafData.stalk Z
                  ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι x))) q},
          ((Module.length (X.presheaf.stalk
            ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι x))
            ((X.presheaf.stalk ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι x)) ⧸
              (Ideal.span {a} ⊔ q.asIdeal)) *
            Module.length (Localization.AtPrime q.asIdeal)
              (LocalizedModule q.asIdeal.primeCompl
                (X.presheaf.stalk ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι x) ⧸
                  IdealSheafData.stalk Z
                    ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι
                      x)))).toNat : ℤ) := by
      rw [hsum]
      apply intCast_toNat_finsum_mem_of_sum_ne_top _
        (finite_minimalSupport (R := X.presheaf.stalk
          ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι x))
          (M := X.presheaf.stalk ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι x) ⧸
            IdealSheafData.stalk Z
              ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι x)))
      rw [← hsum]
      exact Module.length_ne_top_iff.mpr hQ
    simp only [ENat.toNat_mul, Nat.cast_mul] at hlocalInt
    have hqne : ∀ q : PrimeSpectrum
        (X.presheaf.stalk ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι x)),
        Minimal (· ∈ Module.support
          (X.presheaf.stalk ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι x))
          (X.presheaf.stalk ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι x) ⧸
            IdealSheafData.stalk Z
              ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι x))) q →
        q ≠ IsLocalRing.closedPoint
          (X.presheaf.stalk ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι x)) :=
      fun q hq => ne_closedPoint_of_minimal_support_quotient _ hdim1 q hq
    rw [gysin_sum_eq_sum_minimalPrimes_closedSubscheme C p k Z hZ
        (Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))) x hdim a hker hqne havoid,
      intersectionCycleCoeff_comap_eq_length_quotient_sup C p
        (Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))) Z k x a hker ⟨ξ, hξ⟩ hdim,
      ← (quotSMulTopQuotientEquiv a
        (IdealSheafData.stalk Z
          ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι x))).length_eq]
    exact hlocalInt.symm
  · rw [cycleAssociatedToClosedSubscheme_apply_eq_zero C
        ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ p)
      (Z.comap (Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι).subschemeι k x hgen]
    apply finsum_eq_zero_of_forall_eq_zero
    intro y
    by_cases hcy : (cycleAssociatedToClosedSubscheme C
        ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ p)
        (((reducedPointClosure y.1).comap
          (Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι).subschemeι) k).1 x = 0
    · rw [hcy, mul_zero]
    · exfalso
      obtain ⟨ζ, hζ, hyrel⟩ := exists_genericPoint_of_closedSubschemeCycle_ne_zero C p
        Z.subschemeι (k + 1) y.1 y.2
      have hysupp : y.1 ∈ (Z.support : Set X) := hζ ▸ subschemeι_mem_support Z ζ.1
      obtain ⟨ρ, hρ, hdimx⟩ := exists_genericPoint_of_closedSubschemeCycle_ne_zero C
        ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ p)
        (((reducedPointClosure y.1).comap
          (Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι).subschemeι) k x hcy
      have hxr := map_mem_support_of_mem_range_comap
        (Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι (reducedPointClosure y.1)
        (⟨ρ.1, hρ⟩ : x ∈ Set.range _)
      have hclos : (Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι x ∈ closure
          ({y.1} : Set X) := by
        rwa [reducedPointClosure_support] at hxr
      have hxZ : (Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι x ∈
          (Z.support : Set X) :=
        closure_minimal (Set.singleton_subset_iff.mpr hysupp) hZclosed hclos
      obtain ⟨x', hx'⟩ := exists_subschemeι_eq_of_mem_support
        (Z.comap (Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι)
        (by rw [Scheme.IdealSheafData.support_comap]; exact hxZ)
      have hbound := schemeDeltaDimension_comap_le_of_avoid C p k Z
          (Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))) hZ havoid
      have hcomp := isGenericPoint_component_of_top_relativeDimension C
        ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ p) k
          (Z.comap (Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι) hbound x'
          (by rw [hx']; exact hdimx)
      exact hgen ⟨⟨x', hcomp⟩, hx', hdimx⟩

/-- Intersecting a closed subscheme properly with a Cartier zero scheme computes
its Gysin class. -/
@[stacks 02TB "part (1)"]
theorem gysinHomomorphismOfInvertible_cycleAssociatedToClosedSubscheme
    (C : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)
    (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : L.sections) (Z : X.IdealSheafData)
    (hZ : schemeDeltaDimension C (Z.subschemeι ≫ p) ≤
      ((k + 1 : ℤ) : EInt))
    (hDZ : Stacks.Divisors.IsEffectiveCartierDivisor
      ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).comap Z.subschemeι)) :
    gysinHomomorphismOfInvertible C p k L (s.eval (.op ⊤))
        (cycleAssociatedToClosedSubscheme C p Z.subschemeι (k + 1)) =
      QuotientAddGroup.mk
        (cycleAssociatedToClosedSubscheme C
          ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ p)
          ((Z.comap (Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι).subschemeι)
            k) := by
  change QuotientAddGroup.mk ((gysinRule C p k L (s.eval (.op ⊤))
    (firstChernComponentClass C p k L)).extendCycleGroup
      (cycleAssociatedToClosedSubscheme C p Z.subschemeι (k + 1))) = _
  rw [gysinRule_extendCycleGroup_cycleAssociatedToClosedSubscheme C p k L s Z hZ hDZ]


end Stacks.Chow
