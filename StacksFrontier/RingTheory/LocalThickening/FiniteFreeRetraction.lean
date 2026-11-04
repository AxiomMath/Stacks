module

public import Mathlib
public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.LocalRing.Pullback
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Unramified.Field
public import Mathlib.RingTheory.Unramified.Finite
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finite free covers of smooth algebras over a local ring with nilpotent maximal ideal

Let `R` be a local ring whose maximal ideal is nilpotent — an Artinian local ring, for instance
— and let `A` be a finite `R`-algebra. A formally smooth `A`-algebra `D` of finite type with
nonzero fibres need not have an `A`-algebra map to `A`: the residue fields of its fibres are
finite extensions of those of `A`, and they may all be nontrivial. This file supplies the
replacement used to descend infinitesimal lifts from smooth or étale neighbourhoods: a *finite
free* local `R`-algebra `C` with an `A`-algebra map `D ⟶ A ⊗_R C`, and an `R`-linear retraction
`π : C ⟶ R` of the unit, `π 1 = 1`. Such a retraction is not a ring map, but it becomes one on
the elements which are constant modulo a square-zero ideal, and that is all the descent needs.

## Main results

* `Stacks.LocalThickening.exists_algHom_tensorProduct_of_formallySmooth` and its étale case
  `Stacks.LocalThickening.exists_algHom_tensorProduct_of_etale`: the finite free local algebra
  `C` and the map `D ⟶ A ⊗_R C`. The residue field of `C` is a splitting field large enough to
  contain a residue field of every fibre of `D` (finite over the base by Zariski's lemma); `C`
  is built by adjoining roots of monic lifts of minimal polynomials
  (`Stacks.LocalThickening.exists_finite_free_surjective_of_finiteDimensional`), and the map is
  lifted from the reduction of `A ⊗_R C` by formal smoothness.
* `Stacks.LocalThickening.exists_linearMap_retraction_of_free`: a finite free algebra over a
  local ring has an `R`-linear map `π` to `R` with `π 1 = 1`.
* `Stacks.LocalThickening.retraction`: for an `A'`-algebra `B'` with an `A'`-linear `π : B' ⟶ A'`
  satisfying `π 1 = 1`, and an ideal `I` of `A'` with `I ^ 2 = 0`, the restriction of `π` to the
  fibre product `(A' ⧸ I) ×_{B' ⧸ I B'} B'` is a ring map.
* `Stacks.LocalThickening.retraction_comp_diag` and
  `Stacks.LocalThickening.algebraMap_retraction`: that ring map is a retraction of the diagonal
  map from `A'`, and it is compatible with the first projection modulo `I`.

## References

* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM), step (II), which this
  replaces for a base with nilpotent maximal ideal.
-/

@[expose] public section

open IsLocalRing Polynomial Cardinal
open scoped TensorProduct

universe u

namespace Stacks.LocalThickening

/-! ### The retraction on the fibre product -/

section Retraction

variable {A' A B' : Type u} [CommRing A'] [CommRing A] [CommRing B'] [Algebra A' A]
  [Algebra A' B']
variable (π : B' →ₗ[A'] A') (hπ : π 1 = 1) (hsurj : Function.Surjective (algebraMap A' A))
  (hI : RingHom.ker (algebraMap A' A) ^ 2 = ⊥)

/-- The ideal `I B'` of `B'`, for `I` the kernel of `A' ⟶ A`. -/
abbrev extendedIdeal (A' A B' : Type u) [CommRing A'] [CommRing A] [CommRing B'] [Algebra A' A]
    [Algebra A' B'] : Ideal B' :=
  (RingHom.ker (algebraMap A' A)).map (algebraMap A' B')

/-- The map `A ⟶ B' ⧸ I B'` induced by the structure map, `A` being `A' ⧸ I`. -/
noncomputable def quotientStructureMap : A →+* B' ⧸ extendedIdeal A' A B' :=
  (Ideal.quotientMap _ (algebraMap A' B') Ideal.le_comap_map).comp
    (RingHom.quotientKerEquivOfSurjective hsurj).symm.toRingHom

/-- The map `quotientStructureMap` sends the image of `a ∈ A'` in `A` to the class of `a` in
`B' ⧸ I B'`. -/
theorem quotientStructureMap_algebraMap (a : A') :
    quotientStructureMap hsurj (B' := B') (algebraMap A' A a) =
      Ideal.Quotient.mk (extendedIdeal A' A B') (algebraMap A' B' a) := by
  have h : (RingHom.quotientKerEquivOfSurjective hsurj).symm (algebraMap A' A a) =
      Ideal.Quotient.mk (RingHom.ker (algebraMap A' A)) a := by
    rw [RingEquiv.symm_apply_eq]
    rfl
  show Ideal.quotientMap _ (algebraMap A' B') Ideal.le_comap_map
    ((RingHom.quotientKerEquivOfSurjective hsurj).symm (algebraMap A' A a)) = _
  rw [h]
  rfl

/-- `Stacks.LocalThickening.quotientStructureMap` as a map of `A'`-algebras. -/
noncomputable def quotientStructureAlgHom : A →ₐ[A'] B' ⧸ extendedIdeal A' A B' :=
  { quotientStructureMap hsurj (B' := B') with
    commutes' := fun a => quotientStructureMap_algebraMap hsurj a }

/-- The fibre product `A ×_{B' ⧸ I B'} B'`. -/
noncomputable abbrev fibreProduct : Subring (A × B') :=
  (quotientStructureMap hsurj (B' := B')).pullback (Ideal.Quotient.mk (extendedIdeal A' A B'))

/-- The elements `y` of `B'` with `π (b * y) ∈ I` for every `b`; an ideal of `B'`. -/
def retractionIdeal (I : Ideal A') : Ideal B' where
  carrier := {y | ∀ b : B', π (b * y) ∈ I}
  add_mem' {y z} hy hz b := by
    rw [mul_add, map_add]
    exact I.add_mem (hy b) (hz b)
  zero_mem' b := by simp
  smul_mem' c y hy b := by
    rw [smul_eq_mul, ← mul_assoc]
    exact hy (b * c)

/-- An `A'`-linear map `π` pulls out scalars from `A'`. -/
private theorem map_algebraMap_mul (c : A') (z : B') :
    π (algebraMap A' B' c * z) = c * π z := by
  rw [← Algebra.smul_def, map_smul, smul_eq_mul]

/-- An `A'`-linear map `π` with `π 1 = 1` is a retraction of the structure map. -/
private theorem map_algebraMap_eq (hπ : π 1 = 1) (c : A') : π (algebraMap A' B' c) = c := by
  simpa [hπ] using map_algebraMap_mul π c 1

/-- The linear map `π` sends `I B'` into `I`. -/
theorem map_mem_of_mem_extendedIdeal {y : B'} (hy : y ∈ extendedIdeal A' A B') :
    π y ∈ RingHom.ker (algebraMap A' A) := by
  have hle : extendedIdeal A' A B' ≤ retractionIdeal π (RingHom.ker (algebraMap A' A)) := by
    refine Ideal.map_le_iff_le_comap.mpr fun a ha b => ?_
    rw [mul_comm, map_algebraMap_mul]
    exact Ideal.mul_mem_right _ _ ha
  simpa using hle hy 1

include hI in
/-- The product of two elements of `I B'` vanishes. -/
theorem mul_eq_zero_of_mem_extendedIdeal {y z : B'} (hy : y ∈ extendedIdeal A' A B')
    (hz : z ∈ extendedIdeal A' A B') : y * z = 0 := by
  have h : y * z ∈ (RingHom.ker (algebraMap A' A) ^ 2).map (algebraMap A' B') := by
    rw [Ideal.map_pow, pow_two]
    exact Ideal.mul_mem_mul hy hz
  rwa [hI, Ideal.map_bot, Ideal.mem_bot] at h

include hI in
/-- The product of two elements of `I` vanishes. -/
theorem mul_eq_zero_of_mem {a b : A'} (ha : a ∈ RingHom.ker (algebraMap A' A))
    (hb : b ∈ RingHom.ker (algebraMap A' A)) : a * b = 0 := by
  have h : a * b ∈ RingHom.ker (algebraMap A' A) ^ 2 := by
    rw [pow_two]
    exact Ideal.mul_mem_mul ha hb
  rwa [hI, Ideal.mem_bot] at h

/-- An element of the fibre product has second coordinate congruent modulo `I B'` to the image
of any lift of its first coordinate. -/
theorem sub_mem_extendedIdeal (e : fibreProduct hsurj (B' := B')) {a : A'}
    (ha : algebraMap A' A a = e.1.1) :
    e.1.2 - algebraMap A' B' a ∈ extendedIdeal A' A B' := by
  rw [← Ideal.Quotient.eq]
  have he : quotientStructureMap hsurj (B' := B') e.1.1 =
      Ideal.Quotient.mk (extendedIdeal A' A B') e.1.2 := e.2
  rw [← he, ← ha, quotientStructureMap_algebraMap]

include hπ hI in
/-- The retraction is multiplicative on the fibre product. -/
theorem retraction_map_mul (e e' : fibreProduct hsurj (B' := B')) :
    π ((e * e').1.2) = π e.1.2 * π e'.1.2 := by
  obtain ⟨a, ha⟩ := hsurj e.1.1
  obtain ⟨a', ha'⟩ := hsurj e'.1.1
  set y := e.1.2 - algebraMap A' B' a with hy
  set y' := e'.1.2 - algebraMap A' B' a' with hy'
  have hyI : y ∈ extendedIdeal A' A B' := sub_mem_extendedIdeal hsurj e ha
  have hy'I : y' ∈ extendedIdeal A' A B' := sub_mem_extendedIdeal hsurj e' ha'
  have he : e.1.2 = algebraMap A' B' a + y := by rw [hy]; ring
  have he' : e'.1.2 = algebraMap A' B' a' + y' := by rw [hy']; ring
  have hmul : (e * e').1.2 = e.1.2 * e'.1.2 := rfl
  have hyy : y * y' = 0 := mul_eq_zero_of_mem_extendedIdeal hI hyI hy'I
  have hpp : π y * π y' = 0 :=
    mul_eq_zero_of_mem hI (map_mem_of_mem_extendedIdeal π hyI)
      (map_mem_of_mem_extendedIdeal π hy'I)
  rw [hmul, he, he']
  have hexp : (algebraMap A' B' a + y) * (algebraMap A' B' a' + y') =
      algebraMap A' B' (a * a') + algebraMap A' B' a * y' + algebraMap A' B' a' * y +
        y * y' := by
    rw [map_mul]; ring
  rw [hexp, hyy, add_zero, map_add, map_add, map_algebraMap_eq π hπ, map_algebraMap_mul,
    map_algebraMap_mul, map_add, map_add, map_algebraMap_eq π hπ, map_algebraMap_eq π hπ]
  linear_combination (-1 : A') * hpp

/-- **The retraction.** For an `A'`-linear `π : B' ⟶ A'` with `π 1 = 1` and a surjection
`A' ⟶ A` with square-zero kernel `I`, the restriction of `π` to the fibre product
`A ×_{B' ⧸ I B'} B'`, through its second projection, is a ring map. -/
noncomputable def retraction : fibreProduct hsurj (B' := B') →+* A' where
  toFun e := π e.1.2
  map_one' := hπ
  map_mul' e e' := retraction_map_mul π hπ hsurj hI e e'
  map_zero' := by simp
  map_add' e e' := by
    change π (e.1.2 + e'.1.2) = _
    rw [map_add]

/-- The retraction is `π` applied to the second component of an element of the fibre product. -/
theorem retraction_apply (e : fibreProduct hsurj (B' := B')) :
    retraction π hπ hsurj hI e = π e.1.2 := rfl

/-- The diagonal map `A' ⟶ A ×_{B' ⧸ I B'} B'`. -/
noncomputable def diag : A' →+* fibreProduct hsurj (B' := B') :=
  ((algebraMap A' A).prod (algebraMap A' B')).codRestrict _ fun a =>
    (quotientStructureMap_algebraMap hsurj a)

include hπ in
/-- The retraction is a retraction of the diagonal. -/
theorem retraction_comp_diag : (retraction π hπ hsurj hI).comp (diag hsurj) = RingHom.id A' := by
  ext a
  exact map_algebraMap_eq π hπ a

/-- Followed by `A' ⟶ A`, the retraction is the first projection. -/
theorem algebraMap_retraction (e : fibreProduct hsurj (B' := B')) :
    algebraMap A' A (retraction π hπ hsurj hI e) = e.1.1 := by
  obtain ⟨a, ha⟩ := hsurj e.1.1
  have hy := sub_mem_extendedIdeal hsurj e ha
  have hπy := map_mem_of_mem_extendedIdeal π hy
  rw [map_sub, map_algebraMap_eq π hπ, RingHom.mem_ker, map_sub, sub_eq_zero] at hπy
  rw [retraction_apply, hπy, ha]

end Retraction

/-! ### A finite free algebra receiving a map from an étale algebra -/

section FiniteFree

variable {A' C' : Type u} [CommRing A'] [IsLocalRing A'] [CommRing C'] [Algebra A' C']

/-- Over a local ring with nilpotent maximal ideal, the structure map to a field kills the
maximal ideal. -/
theorem algebraMap_eq_zero_of_mem_maximalIdeal (hnil : IsNilpotent (maximalIdeal A'))
    {l : Type u} [Field l] [Algebra A' l] {a : A'} (ha : a ∈ maximalIdeal A') :
    algebraMap A' l a = 0 := by
  obtain ⟨n, hn⟩ := hnil
  have hpow : a ^ n ∈ maximalIdeal A' ^ n := Ideal.pow_mem_pow ha n
  have ha0 : a ^ n = 0 := by
    rw [hn] at hpow
    simpa using hpow
  exact (IsNilpotent.map ⟨n, ha0⟩ (algebraMap A' l)).eq_zero

end FiniteFree

/-! ### Sections of formally smooth algebras after a finite free base change -/


/-- A nilpotent ideal is contained in every prime ideal. -/
private theorem le_of_isNilpotent_of_isPrime {A : Type*} [CommRing A] {N P : Ideal A}
    (hN : IsNilpotent N) (hP : P.IsPrime) : N ≤ P := by
  obtain ⟨n, hn⟩ := hN
  exact hP.le_of_pow_le (by rw [hn]; exact bot_le)

/-- The image of a nilpotent ideal under a ring map is nilpotent. -/
private theorem isNilpotent_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    {I : Ideal R} (hI : IsNilpotent I) : IsNilpotent (I.map f) := by
  obtain ⟨n, hn⟩ := hI
  exact ⟨n, by rw [← Ideal.map_pow, hn]; simp⟩

/-- The adjunction of a root of a monic lift of an irreducible polynomial over the residue field
of a local ring with nilpotent maximal ideal is again a local ring, whose maximal ideal is
generated by the maximal ideal of the base. -/
@[sga "3 V 4.1.2" "special case"]
private theorem isLocalRing_adjoinRoot {R : Type u} [CommRing R] [IsLocalRing R]
    (hR : IsNilpotent (maximalIdeal R)) {F : R[X]} (hirr : Irreducible (F.map (residue R))) :
    ∃ _ : IsLocalRing (AdjoinRoot F),
      (maximalIdeal R).map (AdjoinRoot.of F) = maximalIdeal (AdjoinRoot F) := by
  set N := (maximalIdeal R).map (AdjoinRoot.of F) with hN
  have hfield : IsField (AdjoinRoot F ⧸ N) := by
    have hm : (Ideal.span {F.map (residue R)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible hirr
    exact MulEquiv.isField ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 hm)
      (AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot (maximalIdeal R) F).toMulEquiv
  have hmax : N.IsMaximal := Ideal.Quotient.maximal_of_isField N hfield
  have hnil : IsNilpotent N := isNilpotent_map _ hR
  have hloc : IsLocalRing (AdjoinRoot F) := by
    refine IsLocalRing.of_unique_max_ideal ⟨N, hmax, fun M hM => ?_⟩
    exact (hmax.eq_of_le hM.ne_top (le_of_isNilpotent_of_isPrime hnil hM.isPrime)).symm
  exact ⟨hloc, IsLocalRing.eq_maximalIdeal hmax⟩

/-- The inductive form: a ring map `φ` from a local ring with nilpotent maximal ideal onto a
field `L`, with kernel
the maximal ideal, whose image together with finitely many integral elements generates `L`,
factors through a finite free local algebra mapping onto `L`. -/
private theorem exists_finite_free_of_closure {L : Type u} [Field L] (s : Finset L) :
    ∀ (R : Type u) [CommRing R] [IsLocalRing R], IsNilpotent (maximalIdeal R) → ∀ (φ : R →+* L),
      RingHom.ker φ = maximalIdeal R → (∀ x ∈ s, φ.IsIntegralElem x) →
      Subring.closure (Set.range φ ∪ s) = ⊤ →
      ∃ (C : Type u) (_ : CommRing C) (_ : Algebra R C) (g : C →+* L),
        Module.Free R C ∧ Module.Finite R C ∧ IsLocalRing C ∧ Function.Surjective g ∧
          g.comp (algebraMap R C) = φ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro R _ _ _ φ _ _ hgen
    refine ⟨R, inferInstance, inferInstance, φ, inferInstance, inferInstance, inferInstance,
      ?_, by ext; simp⟩
    intro x
    have hx : x ∈ Subring.closure (Set.range φ ∪ ((∅ : Finset L) : Set L)) := by
      rw [hgen]; trivial
    simp only [Finset.coe_empty, Set.union_empty] at hx
    have : Subring.closure (Set.range φ) = φ.range := by
      rw [← RingHom.coe_range, Subring.closure_eq]
    rw [this] at hx
    exact hx
  | @insert α s hαs ih =>
    intro R _ _ hR φ hker hint hgen
    -- the residue field of `R` embeds in `L`
    have : IsLocalHom φ := ⟨fun r hr => by
      by_contra hu
      have : r ∈ RingHom.ker φ := by rw [hker]; exact hu
      exact hr.ne_zero (RingHom.mem_ker.1 this)⟩
    let ι : ResidueField R →+* L := ResidueField.lift φ
    let : Algebra (ResidueField R) L := ι.toAlgebra
    have hιres : ∀ r, ι (residue R r) = φ r := fun r => ResidueField.lift_residue_apply φ r
    -- `α` is integral over the residue field
    obtain ⟨p, hpm, hp⟩ := hint α (Finset.mem_insert_self α s)
    have hαint : IsIntegral (ResidueField R) α := by
      refine ⟨p.map (residue R), hpm.map _, ?_⟩
      rw [eval₂_map]
      have : (algebraMap (ResidueField R) L).comp (residue R) = φ := by
        ext r; exact hιres r
      rw [this]; exact hp
    set f := minpoly (ResidueField R) α with hf
    obtain ⟨F, hFmap, -, hFm⟩ := lifts_and_degree_eq_and_monic
      (Polynomial.map_surjective _ (residue_surjective (R := R)) f) (minpoly.monic hαint)
    have hirr : Irreducible (F.map (residue R)) := by
      rw [hFmap]; exact minpoly.irreducible hαint
    obtain ⟨hloc, hmaxeq⟩ := isLocalRing_adjoinRoot hR hirr
    have : Module.Finite R (AdjoinRoot F) := hFm.finite_adjoinRoot
    have : Module.Free R (AdjoinRoot F) := Module.Free.of_basis (AdjoinRoot.powerBasis' hFm).basis
    have hR₁ : IsNilpotent (maximalIdeal (AdjoinRoot F)) :=
      hmaxeq ▸ isNilpotent_map _ hR
    have heval : eval₂ φ α F = 0 := by
      have : φ = (algebraMap (ResidueField R) L).comp (residue R) := by
        ext r; exact (hιres r).symm
      rw [this, ← eval₂_map, hFmap]
      exact minpoly.aeval _ _
    let g₁ : AdjoinRoot F →+* L := AdjoinRoot.lift φ α heval
    have hg₁of : g₁.comp (algebraMap R (AdjoinRoot F)) = φ := by
      ext r; exact AdjoinRoot.lift_of heval
    have hg₁root : g₁ (AdjoinRoot.root F) = α := AdjoinRoot.lift_root heval
    -- the kernel of `g₁` is the maximal ideal
    have hkerg₁ : RingHom.ker g₁ = maximalIdeal (AdjoinRoot F) := by
      have hle : maximalIdeal (AdjoinRoot F) ≤ RingHom.ker g₁ := by
        rw [← hmaxeq, Ideal.map_le_iff_le_comap]
        intro r hr
        show g₁ (AdjoinRoot.of F r) = 0
        have : g₁ (AdjoinRoot.of F r) = φ r := AdjoinRoot.lift_of heval
        rw [this, ← RingHom.mem_ker, hker]; exact hr
      exact le_antisymm (IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top g₁)) hle
    have hint₁ : ∀ x ∈ s, g₁.IsIntegralElem x := by
      intro x hx
      obtain ⟨q, hqm, hq⟩ := hint x (Finset.mem_insert_of_mem hx)
      refine ⟨q.map (algebraMap R (AdjoinRoot F)), hqm.map _, ?_⟩
      rw [eval₂_map, hg₁of]; exact hq
    have hgen₁ : Subring.closure (Set.range g₁ ∪ s) = ⊤ := by
      rw [eq_top_iff, ← hgen, Subring.closure_le]
      rintro x (⟨r, rfl⟩ | hx)
      · refine Subring.subset_closure (Or.inl ⟨algebraMap R (AdjoinRoot F) r, ?_⟩)
        exact congrArg (fun h : R →+* L => h r) hg₁of
      · rcases Finset.mem_insert.1 hx with rfl | hx
        · exact Subring.subset_closure (Or.inl ⟨AdjoinRoot.root F, hg₁root⟩)
        · exact Subring.subset_closure (Or.inr hx)
    obtain ⟨C, _, _, g, hfree, hfin, hlocC, hsurj, hcomp⟩ :=
      ih (AdjoinRoot F) hR₁ g₁ hkerg₁ hint₁ hgen₁
    let : Algebra R C := ((algebraMap (AdjoinRoot F) C).comp
      (algebraMap R (AdjoinRoot F))).toAlgebra
    have : IsScalarTower R (AdjoinRoot F) C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have := hfree
    have := hfin
    refine ⟨C, inferInstance, inferInstance, g, Module.Free.trans (R := R) (S := AdjoinRoot F),
      Module.Finite.trans (AdjoinRoot F) C, hlocC, hsurj, ?_⟩
    rw [IsScalarTower.algebraMap_eq R (AdjoinRoot F) C, ← RingHom.comp_assoc, hcomp, hg₁of]

/-- **A finite extension of the residue field of a local ring with nilpotent maximal ideal is the
residue field of a finite free local algebra.** Let `R` be such a local ring and `L` a finite
extension of its residue field. There is a finite free local `R`-algebra `C` together with a
surjection `C → L` restricting on `R` to the residue map followed by the inclusion of the residue
field. The algebra is built by adjoining roots of monic lifts of minimal polynomials of
generators of `L`. -/
@[sga "3 VIA 1.2" "partial"]
theorem exists_finite_free_surjective_of_finiteDimensional (R : Type u) [CommRing R]
    [IsLocalRing R] (hR : IsNilpotent (maximalIdeal R)) (L : Type u) [Field L]
    [Algebra (ResidueField R) L] [FiniteDimensional (ResidueField R) L] :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra R C) (g : C →+* L),
      Module.Free R C ∧ Module.Finite R C ∧ IsLocalRing C ∧ Function.Surjective g ∧
        ∀ r : R, g (algebraMap R C r) = algebraMap (ResidueField R) L (residue R r) := by
  classical
  let φ : R →+* L := (algebraMap (ResidueField R) L).comp (residue R)
  have hker : RingHom.ker φ = maximalIdeal R := by
    ext r
    simp only [φ, RingHom.mem_ker, RingHom.comp_apply, map_eq_zero_iff _
      (algebraMap (ResidueField R) L).injective, residue_eq_zero_iff]
  let b := Module.finBasis (ResidueField R) L
  let s : Finset L := Finset.univ.image b
  have hint : ∀ x ∈ s, φ.IsIntegralElem x := by
    intro x _
    obtain ⟨p, hpm, hp⟩ := Algebra.IsIntegral.isIntegral (R := ResidueField R) x
    obtain ⟨q, hqmap, -, hqm⟩ := lifts_and_degree_eq_and_monic
      (Polynomial.map_surjective _ (residue_surjective (R := R)) p) hpm
    refine ⟨q, hqm, ?_⟩
    rw [show φ = (algebraMap (ResidueField R) L).comp (residue R) from rfl, ← eval₂_map, hqmap]
    exact hp
  have hgen : Subring.closure (Set.range φ ∪ s) = ⊤ := by
    have hrange : Set.range φ = Set.range (algebraMap (ResidueField R) L) := by
      ext x; constructor
      · rintro ⟨r, rfl⟩; exact ⟨_, rfl⟩
      · rintro ⟨y, rfl⟩
        obtain ⟨r, rfl⟩ := residue_surjective y
        exact ⟨r, rfl⟩
    rw [hrange, ← Algebra.adjoin_eq_ring_closure, eq_top_iff]
    intro x _
    have hspan : x ∈ Submodule.span (ResidueField R) (s : Set L) := by
      rw [show (s : Set L) = Set.range b by simp [s]]
      rw [b.span_eq]; trivial
    exact Algebra.span_le_adjoin _ _ hspan
  obtain ⟨C, _, _, g, hfree, hfin, hloc, hsurj, hcomp⟩ :=
    exists_finite_free_of_closure s R hR φ hker hint hgen
  exact ⟨C, inferInstance, inferInstance, g, hfree, hfin, hloc, hsurj,
    fun r => congrArg (fun h : R →+* L => h r) hcomp⟩


/-- **A finite algebra over a local ring with nilpotent maximal ideal has finitely many maximal
ideals and a nilpotent Jacobson radical.** Modulo the nilpotent ideal `𝔪 A` it is a finite
algebra over the residue field, hence Artinian. -/
theorem isNilpotent_jacobson_and_finite_maximalSpectrum_of_finite (R A : Type u) [CommRing R]
    [IsLocalRing R] (hR : IsNilpotent (maximalIdeal R)) [CommRing A] [Algebra R A]
    [Module.Finite R A] :
    IsNilpotent (⊥ : Ideal A).jacobson ∧ Finite (MaximalSpectrum A) := by
  set N := (maximalIdeal R).map (algebraMap R A) with hN
  have hNnil : IsNilpotent N := isNilpotent_map _ hR
  let : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
  have : Module.Finite R (A ⧸ N) := inferInstance
  have : Module.Finite (R ⧸ maximalIdeal R) (A ⧸ N) :=
    Module.Finite.of_restrictScalars_finite R _ _
  have : IsArtinianRing (A ⧸ N) := IsArtinianRing.of_finite (R ⧸ maximalIdeal R) (A ⧸ N)
  refine ⟨?_, ?_⟩
  · obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := A ⧸ N)
    obtain ⟨k, hk⟩ := hNnil
    refine ⟨n * k, ?_⟩
    have hle : (⊥ : Ideal A).jacobson ^ n ≤ N := by
      have hmap : ((⊥ : Ideal A).jacobson ^ n).map (Ideal.Quotient.mk N) ≤ ⊥ := by
        rw [Ideal.map_pow]
        refine (Ideal.pow_right_mono ?_ n).trans hn.le
        have := Ideal.map_jacobson_of_surjective (I := N) (f := Ideal.Quotient.mk N)
          Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker])
        rw [Ideal.map_quotient_self] at this
        rw [← this]
        exact Ideal.map_mono (Ideal.jacobson_mono bot_le)
      intro x hx
      have := hmap (Ideal.mem_map_of_mem _ hx)
      rwa [Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at this
    rw [pow_mul]
    refine eq_bot_iff.2 ((Ideal.pow_right_mono hle k).trans ?_)
    rw [hk]; exact le_rfl
  · have : Finite (PrimeSpectrum (A ⧸ N)) := inferInstance
    have : Finite (PrimeSpectrum A) := by
      refine Finite.of_surjective (PrimeSpectrum.comap (Ideal.Quotient.mk N)) ?_
      intro P
      have hle : RingHom.ker (Ideal.Quotient.mk N) ≤ P.asIdeal := by
        rw [Ideal.mk_ker]; exact le_of_isNilpotent_of_isPrime hNnil P.isPrime
      have := Ideal.map_isPrime_of_surjective (f := Ideal.Quotient.mk N)
        Ideal.Quotient.mk_surjective hle
      refine ⟨⟨P.asIdeal.map (Ideal.Quotient.mk N), inferInstance⟩, ?_⟩
      ext1
      show Ideal.comap _ (Ideal.map _ _) = _
      rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
        sup_eq_left.2 hle]
    exact Finite.of_injective _ MaximalSpectrum.toPrimeSpectrum_injective

/-- A surjection from a local ring onto a field has the maximal ideal as kernel. -/
theorem ker_eq_maximalIdeal_of_surjective {C L : Type*} [CommRing C] [IsLocalRing C]
    [Field L] (g : C →+* L) (hg : Function.Surjective g) :
    RingHom.ker g = maximalIdeal C :=
  IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective g hg)

/-- **A fibre of a finite type algebra over a maximal ideal has a finite residue field.** If `D`
is of finite type over `A` and `m` is a maximal ideal of `A` with `m D ≠ D`, there is a finite
extension `E` of `A ⧸ m` and a ring map `D → E` restricting on `A` to the quotient map followed
by the inclusion (Zariski's lemma). -/
theorem exists_finite_of_finiteType {A D : Type u} [CommRing A] [CommRing D]
    [Algebra A D] [Algebra.FiniteType A D] (m : Ideal A) [m.IsMaximal]
    (hm : Ideal.map (algebraMap A D) m ≠ ⊤) :
    letI : Field (A ⧸ m) := Ideal.Quotient.field m
    ∃ (E : Type u) (_ : Field E) (_ : Algebra (A ⧸ m) E),
      FiniteDimensional (A ⧸ m) E ∧
        ∃ ψ : D →+* E, ψ.comp (algebraMap A D) =
          (algebraMap (A ⧸ m) E).comp (Ideal.Quotient.mk m) := by
  let : Field (A ⧸ m) := Ideal.Quotient.field m
  let F := (A ⧸ m) ⊗[A] D
  have hnt : Nontrivial F := by
    have : Nontrivial (D ⧸ Ideal.map (algebraMap A D) m) := Ideal.Quotient.nontrivial_iff.2 hm
    exact ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot D m).toRingEquiv.trans
      (Algebra.TensorProduct.comm A D (A ⧸ m)).toRingEquiv).symm.nontrivial
  obtain ⟨M, hM⟩ := Ideal.exists_maximal F
  let : Field (F ⧸ M) := Ideal.Quotient.field M
  have : Algebra.FiniteType (A ⧸ m) (F ⧸ M) := inferInstance
  have : Module.Finite (A ⧸ m) (F ⧸ M) := finite_of_finite_type_of_isJacobsonRing _ _
  refine ⟨F ⧸ M, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · exact (Ideal.Quotient.mk M).comp
      (Algebra.TensorProduct.includeRight : D →ₐ[A] F).toRingHom
  · ext a
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Algebra.TensorProduct.includeRight_apply]
    have : (1 : A ⧸ m) ⊗ₜ[A] (algebraMap A D a) =
        algebraMap (A ⧸ m) F (Ideal.Quotient.mk m a) := by
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        Algebra.algebraMap_eq_smul_one a, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
        Algebra.smul_def, mul_one]
      rfl
    rw [this]
    rfl

/-- **A formally smooth finite type algebra over a finite algebra over a local ring with nilpotent
maximal ideal acquires a section after a finite free local base extension.** Let `R` be such a
local ring, `A` a finite `R`-algebra and `D` a formally smooth `A`-algebra of finite type all of
whose fibres over the maximal ideals of `A` are nonzero. There is a finite free local
`R`-algebra `C` and an `A`-algebra map `D → A ⊗_R C`. -/
theorem exists_algHom_tensorProduct_of_formallySmooth (R : Type u) [CommRing R] [IsLocalRing R]
    (hR : IsNilpotent (maximalIdeal R)) (A : Type u) [CommRing A] [Algebra R A] [Module.Finite R A]
    (D : Type u) [CommRing D] [Algebra A D] [Algebra.FormallySmooth A D]
    [Algebra.FiniteType A D]
    (hfib : ∀ m : Ideal A, m.IsMaximal → Ideal.map (algebraMap A D) m ≠ ⊤) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra R C),
      Module.Free R C ∧ Module.Finite R C ∧ IsLocalRing C ∧ Nonempty (D →ₐ[A] A ⊗[R] C) := by
  classical
  have : Finite (MaximalSpectrum A) :=
    (isNilpotent_jacobson_and_finite_maximalSpectrum_of_finite R A hR).2
  have : Fintype (MaximalSpectrum A) := Fintype.ofFinite _
  -- one finite fibre field for each maximal ideal of `A`
  have hE : ∀ m : MaximalSpectrum A,
      let : Field (A ⧸ m.asIdeal) := Ideal.Quotient.field m.asIdeal
      ∃ (E : Type u) (_ : Field E) (_ : Algebra (A ⧸ m.asIdeal) E),
        FiniteDimensional (A ⧸ m.asIdeal) E ∧
          ∃ ψ : D →+* E, ψ.comp (algebraMap A D) =
            (algebraMap (A ⧸ m.asIdeal) E).comp (Ideal.Quotient.mk m.asIdeal) :=
    fun m => exists_finite_of_finiteType m.asIdeal (hfib m.asIdeal m.isMaximal)
  choose E instE instAE hfdE ψ hψ using hE
  let (m : MaximalSpectrum A) : Field (A ⧸ m.asIdeal) := Ideal.Quotient.field m.asIdeal
  -- a basis of each fibre field, and monic polynomials over `R` killing its members
  let bE (m : MaximalSpectrum A) := Module.finBasis (A ⧸ m.asIdeal) (E m)
  let ρ (m : MaximalSpectrum A) : R →+* E m :=
    (algebraMap (A ⧸ m.asIdeal) (E m)).comp
      ((Ideal.Quotient.mk m.asIdeal).comp (algebraMap R A))
  have hρfin : ∀ m, (ρ m).Finite := by
    intro m
    refine RingHom.Finite.comp ?_ (RingHom.Finite.comp
      (RingHom.Finite.of_surjective _ Ideal.Quotient.mk_surjective) ?_)
    · exact RingHom.finite_algebraMap.2 (hfdE m)
    · exact RingHom.finite_algebraMap.2 inferInstance
  have hp : ∀ (m : MaximalSpectrum A) (k : Fin (Module.finrank (A ⧸ m.asIdeal) (E m))),
      ∃ p : Polynomial R, p.Monic ∧ eval₂ (ρ m) (bE m k) p = 0 :=
    fun m k => (hρfin m).to_isIntegral (bE m k)
  choose p hpm hpθ using hp
  -- the splitting field of the product of their reductions
  let P : Polynomial (ResidueField R) :=
    ∏ m : MaximalSpectrum A, ∏ k, (p m k).map (residue R)
  have hPm : P.Monic :=
    monic_prod_of_monic _ _ fun m _ => monic_prod_of_monic _ _ fun k _ => (hpm m k).map _
  let L := P.SplittingField
  obtain ⟨C, _, _, g, hfree, hfin, hlocC, hgsurj, hgcomp⟩ :=
    exists_finite_free_surjective_of_finiteDimensional R hR L
  have := hfree
  have := hfin
  have hC : IsNilpotent (maximalIdeal C) := by
    have := (isNilpotent_jacobson_and_finite_maximalSpectrum_of_finite R C hR).1
    rwa [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at this
  refine ⟨C, inferInstance, inferInstance, hfree, hfin, hlocC, ?_⟩
  -- the residue fields of `T = A ⊗_R C`
  let T := A ⊗[R] C
  obtain ⟨hTnil, hTfin⟩ := isNilpotent_jacobson_and_finite_maximalSpectrum_of_finite R T hR
  have := hTfin
  have : Fintype (MaximalSpectrum T) := Fintype.ofFinite _
  let (n : MaximalSpectrum T) : Field (T ⧸ n.asIdeal) := Ideal.Quotient.field n.asIdeal
  let mn (n : MaximalSpectrum T) : MaximalSpectrum A :=
    ⟨Ideal.comap (algebraMap A T) n.asIdeal,
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := A) n.asIdeal⟩
  let τ (n : MaximalSpectrum T) : A ⧸ (mn n).asIdeal →+* T ⧸ n.asIdeal :=
    Ideal.quotientMap n.asIdeal (algebraMap A T) le_rfl
  have hkerg : RingHom.ker g = maximalIdeal C := ker_eq_maximalIdeal_of_surjective g hgsurj
  let χ (n : MaximalSpectrum T) : C →+* T ⧸ n.asIdeal :=
    (Ideal.Quotient.mk n.asIdeal).comp
      (Algebra.TensorProduct.includeRight : C →ₐ[R] T).toRingHom
  let σ (n : MaximalSpectrum T) : L →+* T ⧸ n.asIdeal :=
    g.liftOfSurjective hgsurj ⟨χ n, fun c hc => by
      rw [hkerg] at hc
      let : Algebra C (T ⧸ n.asIdeal) := (χ n).toAlgebra
      exact algebraMap_eq_zero_of_mem_maximalIdeal hC hc⟩
  have hσ : ∀ n c, σ n (g c) = χ n c := fun n c =>
    RingHom.liftOfSurjective_comp_apply g hgsurj _ c
  -- the two routes from `R` to a residue field of `T` agree
  have hcompat : ∀ (n : MaximalSpectrum T) (r : R),
      τ n (Ideal.Quotient.mk (mn n).asIdeal (algebraMap R A r)) =
        σ n (algebraMap (ResidueField R) L (residue R r)) := by
    intro n r
    rw [← hgcomp, hσ]
    simp only [τ, χ, Ideal.quotientMap_mk, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply]
    congr 1
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      Algebra.algebraMap_eq_smul_one r, Algebra.algebraMap_eq_smul_one r,
      TensorProduct.smul_tmul]
  -- each fibre field embeds in each residue field of `T` over it
  have hext : ∀ n : MaximalSpectrum T, ∃ ε : E (mn n) →+* T ⧸ n.asIdeal,
      ε.comp (algebraMap (A ⧸ (mn n).asIdeal) (E (mn n))) = τ n := by
    intro n
    set m := mn n
    let : Algebra (A ⧸ m.asIdeal) (T ⧸ n.asIdeal) := (τ n).toAlgebra
    have hadj : IntermediateField.adjoin (A ⧸ m.asIdeal) (Set.range (bE m)) = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have hx : x ∈ Submodule.span (A ⧸ m.asIdeal) (Set.range (bE m)) := by
        rw [(bE m).span_eq]; trivial
      have hle : Submodule.span (A ⧸ m.asIdeal) (Set.range (bE m)) ≤
          Subalgebra.toSubmodule
            (IntermediateField.adjoin (A ⧸ m.asIdeal) (Set.range (bE m))).toSubalgebra :=
        Submodule.span_le.2 (IntermediateField.subset_adjoin _ _)
      exact hle hx
    have hsplit : ∀ s ∈ Set.range (bE m), IsIntegral (A ⧸ m.asIdeal) s ∧
        ((minpoly (A ⧸ m.asIdeal) s).map (algebraMap (A ⧸ m.asIdeal) (T ⧸ n.asIdeal))).Splits := by
      rintro _ ⟨k, rfl⟩
      have hint : IsIntegral (A ⧸ m.asIdeal) (bE m k) := IsIntegral.of_finite _ _
      refine ⟨hint, ?_⟩
      let q : Polynomial (A ⧸ m.asIdeal) := (p m k).map (algebraMap R (A ⧸ m.asIdeal))
      have hq0 : q ≠ 0 := ((hpm m k).map _).ne_zero
      have hqθ : aeval (bE m k) q = 0 := by
        rw [aeval_def, eval₂_map]
        exact hpθ m k
      have hmap : q.map (τ n) =
          (((p m k).map (residue R)).map (algebraMap (ResidueField R) L)).map (σ n) := by
        simp only [q, Polynomial.map_map]
        congr 1
        ext r
        simp only [RingHom.comp_apply]
        rw [← hcompat]
        rfl
      have hqs : (q.map (τ n)).Splits := by
        rw [hmap]
        refine Splits.map ?_ (σ n)
        refine Splits.of_dvd (SplittingField.splits P) (hPm.map _).ne_zero ?_
        refine Polynomial.map_dvd _ ?_
        exact (Finset.dvd_prod_of_mem (fun k => (p m k).map (residue R)) (Finset.mem_univ k)).trans
          (Finset.dvd_prod_of_mem (fun m => ∏ k, (p m k).map (residue R)) (Finset.mem_univ m))
      exact Splits.of_dvd hqs (Polynomial.map_ne_zero hq0)
        (Polynomial.map_dvd _ (minpoly.dvd _ _ hqθ))
    obtain ⟨φ⟩ := IntermediateField.nonempty_algHom_of_adjoin_splits hsplit hadj
    exact ⟨φ.toRingHom, φ.comp_algebraMap⟩
  choose ε hε using hext
  let φ (n : MaximalSpectrum T) : D →+* T ⧸ n.asIdeal := (ε n).comp (ψ (mn n))
  have hφ : ∀ n, (φ n).comp (algebraMap A D) =
      (Ideal.Quotient.mk n.asIdeal).comp (algebraMap A T) := by
    intro n
    ext a
    have h1 := congrArg (fun h : A →+* E (mn n) => h a) (hψ (mn n))
    have h2 := congrArg (fun h : A ⧸ (mn n).asIdeal →+* T ⧸ n.asIdeal =>
      h (Ideal.Quotient.mk (mn n).asIdeal a)) (hε n)
    simp only [RingHom.comp_apply] at h1 h2
    simp only [φ, RingHom.comp_apply, h1, h2]
    rfl
  -- the Chinese remainder theorem and the lift along the nilpotent radical
  let J : Ideal T := ⨅ n : MaximalSpectrum T, n.asIdeal
  have hcop : Pairwise (Function.onFun IsCoprime fun n : MaximalSpectrum T => n.asIdeal) := by
    intro n₁ n₂ hne
    rw [Function.onFun, Ideal.isCoprime_iff_sup_eq]
    exact n₁.isMaximal.coprime_of_ne n₂.isMaximal
      (fun h => hne (MaximalSpectrum.ext h))
  let e := Ideal.quotientInfRingEquivPiQuotient (fun n : MaximalSpectrum T => n.asIdeal) hcop
  let Ψ : D →+* T ⧸ J := e.symm.toRingHom.comp (RingHom.pi φ)
  have hΨ : ∀ a : A, Ψ (algebraMap A D a) = algebraMap A (T ⧸ J) a := by
    intro a
    apply e.injective
    simp only [Ψ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.apply_symm_apply]
    funext n
    have := congrArg (fun h : A →+* T ⧸ n.asIdeal => h a) (hφ n)
    simp only [RingHom.comp_apply] at this
    show φ n (algebraMap A D a) = _
    rw [this]
    exact (congrFun (Ideal.quotientInfToPiQuotient_mk (fun n : MaximalSpectrum T => n.asIdeal)
      (algebraMap A T a)) n).symm
  let Ψa : D →ₐ[A] T ⧸ J := { Ψ with commutes' := hΨ }
  have hJnil : IsNilpotent (RingHom.ker (Ideal.Quotient.mkₐ A J).toRingHom) := by
    have hker : RingHom.ker (Ideal.Quotient.mkₐ A J).toRingHom = J := by
      rw [AlgHom.toRingHom_eq_coe, Ideal.Quotient.mkₐ_ker]
    rw [hker]
    have hle : J ≤ (⊥ : Ideal T).jacobson := by
      refine le_sInf fun M hM => ?_
      exact iInf_le (fun n : MaximalSpectrum T => n.asIdeal) ⟨M, hM.2⟩
    obtain ⟨k, hk⟩ := hTnil
    exact ⟨k, eq_bot_iff.2 ((Ideal.pow_right_mono hle k).trans hk.le)⟩
  exact ⟨Algebra.FormallySmooth.liftOfSurjective Ψa (Ideal.Quotient.mkₐ A J)
    (Ideal.Quotient.mkₐ_surjective A J) hJnil⟩


/-- `exists_algHom_tensorProduct_of_formallySmooth` for an étale algebra. -/
theorem exists_algHom_tensorProduct_of_etale (R : Type u) [CommRing R] [IsLocalRing R]
    (hR : IsNilpotent (maximalIdeal R)) (A : Type u) [CommRing A] [Algebra R A] [Module.Finite R A]
    (D : Type u) [CommRing D] [Algebra A D] [Algebra.Etale A D]
    (hfib : ∀ m : Ideal A, m.IsMaximal → Ideal.map (algebraMap A D) m ≠ ⊤) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra R C),
      Module.Free R C ∧ Module.Finite R C ∧ IsLocalRing C ∧ Nonempty (D →ₐ[A] A ⊗[R] C) :=
  exists_algHom_tensorProduct_of_formallySmooth R hR A D hfib

/-- **A finite free algebra over a local ring with a nonzero fibre has a linear retraction
fixing `1`.** -/
theorem exists_linearMap_retraction_of_free {R C : Type u} [CommRing R] [IsLocalRing R]
    [CommRing C] [Algebra R C] [Module.Free R C] [Module.Finite R C] [Nontrivial C] :
    ∃ p : C →ₗ[R] R, p 1 = 1 := by
  classical
  let b := Module.Free.chooseBasis R C
  by_contra hno
  push Not at hno
  -- every coordinate of `1` lies in the maximal ideal
  have hcoord : ∀ i, b.repr 1 i ∈ maximalIdeal R := by
    intro i
    by_contra hi
    have hu : IsUnit (b.repr 1 i) := by
      by_contra h; exact hi h
    refine hno (hu.unit⁻¹.1 • (b.coord i)) ?_
    simp [Module.Basis.coord_apply]
  have h1 : (1 : C) ∈ (maximalIdeal R) • (⊤ : Submodule R C) := by
    rw [← b.sum_repr 1]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hcoord i) trivial
  have hmap : Ideal.map (algebraMap R C) (maximalIdeal R) = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    have := h1
    rwa [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem] at this
  have htop : (⊤ : Submodule R C) ≤ (maximalIdeal R) • ⊤ := by
    rw [Ideal.smul_top_eq_map, hmap]
    exact le_rfl
  have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) ⊤
    Module.Finite.fg_top htop (by rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top])
  exact top_ne_bot hbot



end Stacks.LocalThickening
