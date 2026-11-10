module

public import Mathlib
public import StacksFrontier.FieldTheory.Separable.Defs
public import StacksFrontier.FieldTheory.Separable.TFAE
public import StacksFrontier.RingTheory.DiscreteValuationRing.BaseChangeClosure
public import StacksFrontier.RingTheory.DiscreteValuationRing.FormallySmoothExtension
public import StacksFrontier.RingTheory.DiscreteValuationRing.Solution
public import StacksFrontier.RingTheory.FormallySmooth.Field
public import StacksFrontier.RingTheory.FormallySmooth.Topological
public import StacksFrontier.RingTheory.IntegralClosure.Pi

/-!
# Descent and composition of solutions for extensions of discrete valuation rings

For a tower `A → B → C` of extensions of discrete valuation rings, a finite extension of the
fraction field of `A` which is a weak solution, or a solution, for `A → C` has the same property
for `A → B`. Conversely, a solution for `A → B` composes with solutions for `B → C` on all field
factors of the reduced tensor product.

## Main definitions

* `IsDiscreteValuationRing.baseClosureEquiv`: the identification of the two presentations of the
  lower integral closure.
* `IsDiscreteValuationRing.reducedCompositumMap` and
  `IsDiscreteValuationRing.targetClosureMap`: the canonical comparison maps for the tower, built
  from the data already supplied by the base-change packages.

## Main results

* `IsDiscreteValuationRing.weakSolutions_and_solutions_go_down_and_compose`: descent and
  composition for weak solutions and solutions.

## Implementation notes

The integral closures and reduced tensor products are represented by the base-change packages
`IsDiscreteValuationRing.IntegralClosureBaseChange`. In the composition assertion, the product
decomposition of the intermediate reduced tensor product is explicit, as are the base-change
packages belonging to its field factors. The packages already characterize the canonical integral
closures and their embeddings, so the comparison constructions below require no extra
compatibility or flatness hypotheses; those are not assumptions of the source lemma. All ring,
field, and presentation universes are independent. Each solution uses formal smoothness at the
maximum of its two integral-closure carrier universes, which are also the universes of their
localizations. This matches the residue-field separability characterization of Tag 09E7 used by
the source proof.

## References

* [The Stacks Project, Tag 09ES](https://stacks.math.columbia.edu/tag/09ES)
-/

@[expose] public section

namespace IsDiscreteValuationRing

section

universe uA uB uC uK uL uM uK₁ uE uL₁ uA₁ uB₁ uM₁ uA₂ uC₁ uN₁ uB₂ uC₂ u v w t u₅ u₆

open scoped TensorProduct

section Comparison
variable
    (A : Type uA) (B : Type uB) (C : Type uC)
    (K : Type uK) (L : Type uL) (M : Type uM) (K₁ : Type uK₁)
    [CommRing A] [CommRing B] [CommRing C]
    [IsDomain A] [IsDomain B] [IsDomain C]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [IsDiscreteValuationRing C]
    [Field K] [Field L] [Field M] [Field K₁]
    [Algebra A B] [Algebra A C]
    [Algebra A K] [Algebra A L] [Algebra A M]
    [Algebra B L] [Algebra C M]
    [Algebra K L] [Algebra K M] [Algebra L M]
    [Algebra K K₁] [Algebra A K₁]
    [IsExtension A B]
    [IsExtension A C]
    [IsFractionRing A K] [IsFractionRing B L] [IsFractionRing C M]
    [IsScalarTower A B L]
    [IsScalarTower A C M]
    [IsScalarTower A K L] [IsScalarTower A K M] [IsScalarTower K L M]
    [IsScalarTower A K K₁] [Module.Finite K K₁]
    (DAB : IntegralClosureBaseChange.{uA, uB, uK, uL, uK₁, uL₁, uA₁, uB₁}
      A B K L K₁)
    (DAC : IntegralClosureBaseChange.{uA, uC, uK, uM, uK₁, uM₁, uA₂, uC₁}
      A C K M K₁)

attribute [local instance]
  IntegralClosureBaseChange.commRingL₁
  IntegralClosureBaseChange.commRingA₁
  IntegralClosureBaseChange.commRingB₁
  IntegralClosureBaseChange.algebraKL₁
  IntegralClosureBaseChange.algebraLL₁
  IntegralClosureBaseChange.algebraK₁L₁
  IntegralClosureBaseChange.algebraBL₁
  IntegralClosureBaseChange.algebraAA₁
  IntegralClosureBaseChange.algebraA₁K₁
  IntegralClosureBaseChange.algebraBB₁
  IntegralClosureBaseChange.algebraB₁L₁
  IntegralClosureBaseChange.algebraAB₁
  IntegralClosureBaseChange.algebraA₁B₁
  IntegralClosureBaseChange.isScalarTowerKLL₁
  IntegralClosureBaseChange.isScalarTowerKK₁L₁
  IntegralClosureBaseChange.isScalarTowerBLL₁
  IntegralClosureBaseChange.isScalarTowerAA₁K₁
  IntegralClosureBaseChange.isScalarTowerBB₁L₁
  IntegralClosureBaseChange.isScalarTowerABB₁
  IntegralClosureBaseChange.isScalarTowerAA₁B₁
  IntegralClosureBaseChange.isIntegralClosureA₁
  IntegralClosureBaseChange.isIntegralClosureB₁

variable {A B C K L M K₁}

/-- The two presentations of the integral closure of `A` in `K₁` are canonically isomorphic. -/
noncomputable def baseClosureEquiv : DAB.A₁ ≃ₐ[A] DAC.A₁ :=
  IsIntegralClosure.equiv A DAB.A₁ K₁ DAC.A₁

/-- The map of reduced tensor products induced by `L → M`, transported to the packages. -/
noncomputable def reducedCompositumMap : DAB.L₁ →ₐ[K] DAC.L₁ := by
  let f := Algebra.TensorProduct.map (IsScalarTower.toAlgHom K L M) (AlgHom.id K K₁)
  let g := Ideal.quotientMapₐ (nilradical (M ⊗[K] K₁)) f (fun x hx =>
    mem_nilradical.mpr ((mem_nilradical.mp hx).map f))
  exact DAC.eL₁.symm.toAlgHom.comp (g.comp DAB.eL₁.toAlgHom)

/-- The map of reduced composita respects the embedding of `L`. -/
lemma reducedCompositumMap_left (x : L) :
    reducedCompositumMap DAB DAC (algebraMap L DAB.L₁ x) =
      algebraMap M DAC.L₁ (algebraMap L M x) := by
  apply DAC.eL₁.injective
  simp [reducedCompositumMap, Ideal.quotientMapₐ, Ideal.quotientMap, DAB.eL₁_left, DAC.eL₁_left,
    Algebra.TensorProduct.includeLeft_apply]

/-- The map of reduced composita respects the embedding of `K₁`. -/
lemma reducedCompositumMap_right (x : K₁) :
    reducedCompositumMap DAB DAC (algebraMap K₁ DAB.L₁ x) =
      algebraMap K₁ DAC.L₁ x := by
  apply DAC.eL₁.injective
  simp [reducedCompositumMap, Ideal.quotientMapₐ, Ideal.quotientMap, DAB.eL₁_right, DAC.eL₁_right,
    Algebra.TensorProduct.includeRight_apply]

variable [Algebra B C] [Algebra B M] [IsScalarTower B C M] [IsScalarTower B L M]

/-- The map of reduced composita is compatible with `B → C`. -/
lemma reducedCompositumMap_base (x : B) :
    reducedCompositumMap DAB DAC (algebraMap B DAB.L₁ x) =
      algebraMap C DAC.L₁ (algebraMap B C x) := by
  rw [IsScalarTower.algebraMap_apply B L DAB.L₁, reducedCompositumMap_left,
    ← IsScalarTower.algebraMap_apply B L M,
    IsScalarTower.algebraMap_apply C M DAC.L₁,
    ← IsScalarTower.algebraMap_apply B C M]

/-- The canonical map between the upper integral closures in a tower. Its existence follows
from preservation of integral elements, without additional compatibility hypotheses. -/
noncomputable def targetClosureMap : DAB.B₁ →+* DAC.B₁ := by
  let f := reducedCompositumMap DAB DAC
  have hf : (algebraMap C DAC.L₁).comp (algebraMap B C) =
      f.toRingHom.comp (algebraMap B DAB.L₁) :=
    RingHom.ext (fun x => (reducedCompositumMap_base DAB DAC x).symm)
  let g (x : DAB.B₁) : DAC.B₁ := IsIntegralClosure.mk' DAC.B₁
    (f (algebraMap DAB.B₁ DAB.L₁ x))
    (IsIntegral.map_of_comp_eq (algebraMap B C) f.toRingHom hf
      (IsIntegralClosure.isIntegral_iff.mpr ⟨x, rfl⟩))
  have hg (x : DAB.B₁) : algebraMap DAC.B₁ DAC.L₁ (g x) =
      f (algebraMap DAB.B₁ DAB.L₁ x) := IsIntegralClosure.algebraMap_mk' (R := C) _ _ _
  exact
    { toFun := g
      map_one' := IsIntegralClosure.algebraMap_injective DAC.B₁ C DAC.L₁ (by simp [hg])
      map_zero' := IsIntegralClosure.algebraMap_injective DAC.B₁ C DAC.L₁ (by simp [hg])
      map_add' := fun x y =>
        IsIntegralClosure.algebraMap_injective DAC.B₁ C DAC.L₁ (by simp [hg])
      map_mul' := fun x y =>
        IsIntegralClosure.algebraMap_injective DAC.B₁ C DAC.L₁ (by simp [hg]) }

/-- The comparison map commutes with the embeddings into the reduced composita. -/
lemma targetClosureMap_algebraMap (x : DAB.B₁) :
    algebraMap DAC.B₁ DAC.L₁ (targetClosureMap DAB DAC x) =
      reducedCompositumMap DAB DAC (algebraMap DAB.B₁ DAB.L₁ x) := by
  simp [targetClosureMap]

/-- The comparison map of integral closures extends `B → C`. -/
lemma targetClosureMap_base (x : B) :
    targetClosureMap DAB DAC (algebraMap B DAB.B₁ x) =
      algebraMap C DAC.B₁ (algebraMap B C x) := by
  apply IsIntegralClosure.algebraMap_injective DAC.B₁ C DAC.L₁
  rw [targetClosureMap_algebraMap, ← IsScalarTower.algebraMap_apply B DAB.B₁ DAB.L₁,
    reducedCompositumMap_base, ← IsScalarTower.algebraMap_apply C DAC.B₁ DAC.L₁]

/-- The integral-closure comparison maps form the commutative square needed for the
localized tower, after identifying the two presentations of the lower integral closure. -/
lemma targetClosureMap_commutes (x : DAB.A₁) :
    targetClosureMap DAB DAC (algebraMap DAB.A₁ DAB.B₁ x) =
      algebraMap DAC.A₁ DAC.B₁ (baseClosureEquiv DAB DAC x) := by
  apply IsIntegralClosure.algebraMap_injective DAC.B₁ C DAC.L₁
  rw [targetClosureMap_algebraMap, DAB.ringSquare, DAC.ringSquare,
    reducedCompositumMap_right, baseClosureEquiv, IsIntegralClosure.algebraMap_equiv]

end Comparison

open IsLocalRing

/-- **Ramification index one is weak unramifiedness.**

For a prime `q` of `S` over `R`, the ramification index `q.ramificationIdx R` is `1` exactly
when the induced extension of local rings at `q` is weakly unramified. This is the bridge
between `Ideal.ramificationIdx`, which `IsWeakSolution` is phrased with, and
`IsDiscreteValuationRing.IsWeaklyUnramified`, which every structural lemma about extensions of
discrete valuation rings is phrased with. -/
theorem ramificationIdx_eq_one_iff_isWeaklyUnramified {R S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] (q : Ideal S) [q.IsPrime]
    [IsDomain (Localization.AtPrime (q.under R))]
    [IsDiscreteValuationRing (Localization.AtPrime (q.under R))]
    [IsDomain (Localization.AtPrime q)] [IsDiscreteValuationRing (Localization.AtPrime q)] :
    letI := Localization.AtPrime.algebraOfLiesOver (q.under R) q
    ∀ [IsExtension (Localization.AtPrime (q.under R)) (Localization.AtPrime q)],
      q.ramificationIdx R = 1 ↔
        IsWeaklyUnramified (Localization.AtPrime (q.under R))
          (Localization.AtPrime q) := by
  let := Localization.AtPrime.algebraOfLiesOver (q.under R) q
  intro _
  rw [weaklyUnramified_iff_map_maximalIdeal, Ideal.ramificationIdx_def,
    ENat.toNat_eq_iff_eq_natCast, Nat.cast_one, Module.length_eq_one_iff,
    isSimpleModule_iff_isCoatom, ← Ideal.isMaximal_def, IsLocalRing.isMaximal_iff,
    IsScalarTower.algebraMap_eq R (Localization.AtPrime (q.under R)) (Localization.AtPrime q),
    ← Ideal.map_map, Localization.AtPrime.map_eq_maximalIdeal]

private theorem isWeaklyUnramified_of_bijective (A : Type u) (B : Type v)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B] [IsDomain B]
    [IsDiscreteValuationRing B] [Algebra A B] [IsExtension A B]
    (h : Function.Bijective (algebraMap A B)) : IsWeaklyUnramified A B := by
  obtain ⟨-, -, h3, -⟩ := ramificationIndex_characterization A B
  unfold IsWeaklyUnramified
  refine (h3 1 le_rfl ?_).symm
  rw [pow_one]
  let e := RingEquiv.ofBijective _ h
  have := Ideal.map_isMaximal_of_equiv e (p := IsLocalRing.maximalIdeal A)
  exact IsLocalRing.eq_maximalIdeal this

private theorem formallySmoothNAdic_of_bijective (A : Type u) (B : Type v)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B] [IsDomain B]
    [IsDiscreteValuationRing B] [Algebra A B] [IsExtension A B]
    (h : Function.Bijective (algebraMap A B)) :
    RingHom.FormallySmoothNAdic.{max u v} (algebraMap A B) (IsLocalRing.maximalIdeal B) := by
  refine (formallySmooth_iff_weaklyUnramified_and_isSeparableExtension A B).mpr
    ⟨isWeaklyUnramified_of_bijective A B h, ?_⟩
  have hb : Function.Bijective (algebraMap (ResidueField A) (ResidueField B)) := by
    refine ⟨(algebraMap (ResidueField A) (ResidueField B)).injective, ?_⟩
    intro y
    obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨x, rfl⟩ := h.2 y
    exact ⟨IsLocalRing.residue A x, rfl⟩
  have : Algebra.FormallySmooth (ResidueField A) (ResidueField B) :=
    Algebra.FormallySmooth.of_equiv (AlgEquiv.ofBijective (Algebra.ofId _ _) hb)
  exact (Algebra.FormallySmooth.iff_isSeparableExtension _ _).mp this

private theorem injective_of_comp_injective {R' R S : Type*} [CommRing R'] [IsDomain R']
    [IsDiscreteValuationRing R'] [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] (h : R' →+* R) [IsLocalHom h] (g : R →+* S)
    (hgh : Function.Injective (g.comp h)) : Function.Injective g := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra hne
  have hker : RingHom.ker g ≠ ⊥ := fun hb => hne (by
    have : x ∈ RingHom.ker g := hx
    rw [hb] at this; exact this)
  have hmax : RingHom.ker g = IsLocalRing.maximalIdeal R := by
    rcases IsDiscreteValuationRing.iff_pid_with_one_nonzero_prime R |>.mp inferInstance with
      ⟨-, P, -, hP⟩
    rw [hP _ ⟨hker, RingHom.ker_isPrime g⟩,
      hP _ ⟨IsDiscreteValuationRing.not_a_field R, (IsLocalRing.maximalIdeal.isMaximal R).isPrime⟩]
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R'
  have hmem : h π ∈ RingHom.ker g := by
    rw [hmax]
    exact (map_mem_nonunits_iff h π).mpr hπ.not_isUnit
  exact hπ.ne_zero (hgh (by simpa using hmem))

private theorem local_tower_descent (R : Type u) (R' : Type v) (S : Type w) (T : Type t)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    (a : R →+* S) (b : S →+* T) (c : R →+* R') (d : R' →+* T)
    [IsLocalHom a] [IsLocalHom b] [IsLocalHom d]
    (hc : Function.Bijective c) (ha : Function.Injective a) (hd : Function.Injective d)
    (hcomm : b.comp a = d.comp c) :
    letI := a.toAlgebra
    letI := d.toAlgebra
    ∀ [IsExtension R S] [IsExtension R' T],
    (IsWeaklyUnramified R' T → IsWeaklyUnramified R S) ∧
      (RingHom.FormallySmoothNAdic.{max v t} d (IsLocalRing.maximalIdeal T) →
        RingHom.FormallySmoothNAdic.{max u w} a (IsLocalRing.maximalIdeal S)) := by
  intro _ _
  have : IsLocalHom c := by
    have : IsLocalHom (d.comp c) := hcomm ▸ inferInstance
    exact isLocalHom_of_comp c d
  have hbinj : Function.Injective b :=
    injective_of_comp_injective a b (by rw [hcomm]; exact hd.comp hc.1)
  let := a.toAlgebra
  let := b.toAlgebra
  let := d.toAlgebra
  let := c.toAlgebra
  let : Algebra R T := (b.comp a).toAlgebra
  have : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : IsScalarTower R R' T := IsScalarTower.of_algebraMap_eq
    (fun x => (RingHom.congr_fun hcomm x :))
  have : IsLocalHom (algebraMap R T) := by
    change IsLocalHom (b.comp a); infer_instance
  have hRT : IsExtension R T :=
    { toFaithfulSMul := (faithfulSMul_iff_algebraMap_injective R T).mpr (hbinj.comp ha) }
  have hRR' : IsExtension R R' :=
    { toFaithfulSMul := (faithfulSMul_iff_algebraMap_injective R R').mpr hc.1 }
  have hST : IsExtension S T :=
    { toFaithfulSMul := (faithfulSMul_iff_algebraMap_injective S T).mpr hbinj }
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact isWeaklyUnramified_tower_bot R S T (isWeaklyUnramified_trans R R' T
      (isWeaklyUnramified_of_bijective R R' hc) h)
  · exact formallySmoothNAdic_tower_bot R S T (formallySmoothNAdic_trans R R' T
      (formallySmoothNAdic_of_bijective R R' hc) h)

private theorem localRingHom_injective {R S : Type*} [CommRing R] [IsDomain R] [CommRing S]
    (f : R →+* S) (hf : ∀ r : R, r ≠ 0 → f r ∈ nonZeroDivisors S)
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] (h : p = q.comap f) :
    Function.Injective (Localization.localRingHom p q f h) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl x
  rw [Localization.localRingHom_mk', IsLocalization.mk'_eq_zero_iff] at hx
  obtain ⟨⟨t, ht⟩, hts⟩ := hx
  by_cases hr : r = 0
  · simp [hr]
  · exfalso
    have : t = 0 := (hf r hr).2 t hts
    exact ht (this ▸ q.zero_mem)

attribute [local instance]
  IntegralClosureBaseChange.commRingL₁
  IntegralClosureBaseChange.commRingA₁
  IntegralClosureBaseChange.commRingB₁
  IntegralClosureBaseChange.algebraKL₁
  IntegralClosureBaseChange.algebraLL₁
  IntegralClosureBaseChange.algebraK₁L₁
  IntegralClosureBaseChange.algebraBL₁
  IntegralClosureBaseChange.algebraAA₁
  IntegralClosureBaseChange.algebraA₁K₁
  IntegralClosureBaseChange.algebraBB₁
  IntegralClosureBaseChange.algebraB₁L₁
  IntegralClosureBaseChange.algebraAB₁
  IntegralClosureBaseChange.algebraA₁B₁
  IntegralClosureBaseChange.isScalarTowerKLL₁
  IntegralClosureBaseChange.isScalarTowerKK₁L₁
  IntegralClosureBaseChange.isScalarTowerBLL₁
  IntegralClosureBaseChange.isScalarTowerAA₁K₁
  IntegralClosureBaseChange.isScalarTowerBB₁L₁
  IntegralClosureBaseChange.isScalarTowerABB₁
  IntegralClosureBaseChange.isScalarTowerAA₁B₁
  IntegralClosureBaseChange.isIntegralClosureA₁
  IntegralClosureBaseChange.isIntegralClosureB₁

private theorem localizations_isDiscreteValuationRing
    {A : Type uA} {B : Type uB} {K : Type uK} {L : Type uL} {K₁ : Type uK₁}
    [CommRing A] [CommRing B] [Field K] [Field L] [Field K₁]
    [IsDomain A] [IsDomain B] [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L]
    [Algebra K L] [Algebra K K₁] [Algebra A K₁]
    [IsExtension A B] [IsFractionRing A K] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsScalarTower A K K₁]
    [Module.Finite K K₁]
    (D : IntegralClosureBaseChange.{uA, uB, uK, uL, uK₁, uL₁, uA₁, uB₁} A B K L K₁)
    (q : Ideal D.B₁) (hq : q.IsMaximal) :
    (q.comap (algebraMap D.A₁ D.B₁)).IsMaximal ∧
      ∃ (_ : IsDomain (Localization.AtPrime (q.comap (algebraMap D.A₁ D.B₁)))),
        IsDiscreteValuationRing (Localization.AtPrime (q.comap (algebraMap D.A₁ D.B₁))) ∧
      ∃ (_ : IsDomain (Localization.AtPrime q)),
        IsDiscreteValuationRing (Localization.AtPrime q) := by
  have hfield : ∀ x : K, algebraMap L D.L₁ (algebraMap K L x) =
      algebraMap K₁ D.L₁ (algebraMap K K₁ x) := fun x => by
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have h := integralClosures_after_finite_fraction_field_extension A B K L K₁
    D.L₁ D.A₁ D.B₁ D.eL₁ (IsIntegralClosure.equiv A D.A₁ K₁ (integralClosure A K₁))
    (IsIntegralClosure.equiv B D.B₁ D.L₁ (integralClosure B D.L₁))
    D.eL₁_left D.eL₁_right
    (fun x => IsIntegralClosure.algebraMap_equiv B D.B₁ D.L₁ (integralClosure B D.L₁) x) hfield
    (fun x => by
      rw [D.ringSquare]
      exact congrArg _ (IsIntegralClosure.algebraMap_equiv A D.A₁ K₁ (integralClosure A K₁) x).symm)
  obtain ⟨-, -, -, -, -, -, -, -, -, h10, -⟩ := h
  obtain ⟨hmax, _, _, ⟨hd1, hdvr1⟩, ⟨hd2, hdvr2⟩, -⟩ := h10 q hq
  exact ⟨hmax, hd1, hdvr1, hd2, hdvr2⟩

private theorem isNonZeroDivisor_algebraMap
    {A : Type uA} {B : Type uB} {K : Type uK} {L : Type uL} {K₁ : Type uK₁}
    [CommRing A] [CommRing B] [Field K] [Field L] [Field K₁]
    [IsDomain A] [IsDomain B] [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L]
    [Algebra K L] [Algebra K K₁] [Algebra A K₁]
    [IsExtension A B] [IsFractionRing A K] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsScalarTower A K K₁]
    [Module.Finite K K₁]
    (D : IntegralClosureBaseChange.{uA, uB, uK, uL, uK₁, uL₁, uA₁, uB₁} A B K L K₁)
    [Nontrivial D.L₁] (r : D.A₁) (hr : r ≠ 0) :
    algebraMap D.A₁ D.B₁ r ∈ nonZeroDivisors D.B₁ := by
  have hK : algebraMap D.A₁ K₁ r ≠ 0 := fun h =>
    hr (IsIntegralClosure.algebraMap_injective D.A₁ A K₁ (by simpa using h))
  have hu : IsUnit (algebraMap D.B₁ D.L₁ (algebraMap D.A₁ D.B₁ r)) := by
    rw [D.ringSquare]; exact (Ne.isUnit hK).map _
  have hinj := IsIntegralClosure.algebraMap_injective D.B₁ B D.L₁
  refine mem_nonZeroDivisors_iff.mpr ⟨fun x hx => hinj ?_, fun x hx => hinj ?_⟩
  · rw [map_zero]
    exact (hu.mul_left_eq_zero).mp (by rw [← map_mul, mul_comm, hx, map_zero])
  · rw [map_zero]
    exact (hu.mul_right_eq_zero).mp (by rw [← map_mul, mul_comm, hx, map_zero])

private theorem localTower_descent
    {A : Type uA} {B : Type uB} {C : Type uC}
    {K : Type uK} {L : Type uL} {M : Type uM} {K₁ : Type uK₁}
    [CommRing A] [CommRing B] [CommRing C]
    [IsDomain A] [IsDomain B] [IsDomain C]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [IsDiscreteValuationRing C]
    [Field K] [Field L] [Field M] [Field K₁]
    [Algebra A B] [Algebra A C]
    [Algebra A K] [Algebra A L] [Algebra A M]
    [Algebra B L] [Algebra C M]
    [Algebra K L] [Algebra K M] [Algebra L M]
    [Algebra K K₁] [Algebra A K₁]
    [IsExtension A B]
    [IsExtension A C]
    [IsFractionRing A K] [IsFractionRing B L] [IsFractionRing C M]
    [IsScalarTower A B L]
    [IsScalarTower A C M]
    [IsScalarTower A K L] [IsScalarTower A K M] [IsScalarTower K L M]
    [IsScalarTower A K K₁] [Module.Finite K K₁]
    [Algebra B C] [Algebra B M] [IsScalarTower B C M] [IsScalarTower B L M]
    (DAB : IntegralClosureBaseChange.{uA, uB, uK, uL, uK₁, uL₁, uA₁, uB₁}
      A B K L K₁)
    (DAC : IntegralClosureBaseChange.{uA, uC, uK, uM, uK₁, uM₁, uA₂, uC₁}
      A C K M K₁)
    (q : Ideal DAB.B₁) [hq : q.IsMaximal] (Q : Ideal DAC.B₁) [hQ : Q.IsMaximal]
    (hQq : Q.comap (targetClosureMap DAB DAC) = q) :
    let := Localization.AtPrime.algebraOfLiesOver (q.under DAB.A₁) q
letI := Localization.AtPrime.algebraOfLiesOver (Q.under DAC.A₁) Q
∃ (_ : IsDomain (Localization.AtPrime (q.under DAB.A₁)))
  (_ : IsDiscreteValuationRing (Localization.AtPrime (q.under DAB.A₁)))
  (_ : IsDomain (Localization.AtPrime q)) (_ : IsDiscreteValuationRing (Localization.AtPrime q))
  (_ : IsDomain (Localization.AtPrime (Q.under DAC.A₁)))
  (_ : IsDiscreteValuationRing (Localization.AtPrime (Q.under DAC.A₁)))
  (_ : IsDomain (Localization.AtPrime Q)) (_ : IsDiscreteValuationRing (Localization.AtPrime Q))
  (_ : IsExtension (Localization.AtPrime (q.under DAB.A₁)) (Localization.AtPrime q))
  (_ : IsExtension (Localization.AtPrime (Q.under DAC.A₁)) (Localization.AtPrime Q)),
  (IsWeaklyUnramified (Localization.AtPrime (Q.under DAC.A₁)) (Localization.AtPrime Q) →
    IsWeaklyUnramified (Localization.AtPrime (q.under DAB.A₁)) (Localization.AtPrime q)) ∧
  (RingHom.FormallySmoothNAdic.{max uA₂ uC₁}
      (algebraMap (Localization.AtPrime (Q.under DAC.A₁)) (Localization.AtPrime Q))
      (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) →
    RingHom.FormallySmoothNAdic.{max uA₁ uB₁}
      (algebraMap (Localization.AtPrime (q.under DAB.A₁)) (Localization.AtPrime q))
      (IsLocalRing.maximalIdeal (Localization.AtPrime q))) := by
  have : Nontrivial DAB.L₁ := by
    have : Nontrivial DAB.B₁ := ⟨⟨0, 1, fun h => hq.ne_top ((Ideal.eq_top_iff_one q).mpr (h ▸
      q.zero_mem))⟩⟩
    exact (IsIntegralClosure.algebraMap_injective DAB.B₁ B DAB.L₁).nontrivial
  have : Nontrivial DAC.L₁ := by
    have : Nontrivial DAC.B₁ := ⟨⟨0, 1, fun h => hQ.ne_top ((Ideal.eq_top_iff_one Q).mpr (h ▸
      Q.zero_mem))⟩⟩
    exact (IsIntegralClosure.algebraMap_injective DAC.B₁ C DAC.L₁).nontrivial
  obtain ⟨-, hd1, hv1, hd2, hv2⟩ := localizations_isDiscreteValuationRing DAB q hq
  obtain ⟨-, hd3, hv3, hd4, hv4⟩ := localizations_isDiscreteValuationRing DAC Q hQ
  let e := baseClosureEquiv DAB DAC
  let f := targetClosureMap DAB DAC
  have hsq : f.comp (algebraMap DAB.A₁ DAB.B₁) =
      (algebraMap DAC.A₁ DAC.B₁).comp (e : DAB.A₁ →+* DAC.A₁) :=
    RingHom.ext (targetClosureMap_commutes DAB DAC)
  have hpq : q.under DAB.A₁ = (Q.under DAC.A₁).comap (e : DAB.A₁ →+* DAC.A₁) := by
    change _ = Ideal.comap _ (Ideal.comap _ Q)
    rw [Ideal.comap_comap, ← hsq, ← Ideal.comap_comap, hQq]
  let a := Localization.localRingHom (q.under DAB.A₁) q (algebraMap DAB.A₁ DAB.B₁) rfl
  let d := Localization.localRingHom (Q.under DAC.A₁) Q (algebraMap DAC.A₁ DAC.B₁) rfl
  let b := Localization.localRingHom q Q f hQq.symm
  let c := Localization.localRingHom (q.under DAB.A₁) (Q.under DAC.A₁)
    (e : DAB.A₁ →+* DAC.A₁) hpq
  have hcbij : Function.Bijective c :=
    (Localization.localRingEquiv (q.under DAB.A₁) (Q.under DAC.A₁) e.toRingEquiv hpq).bijective
  have hcomm : b.comp a = d.comp c := by
    apply IsLocalization.ringHom_ext (q.under DAB.A₁).primeCompl
    ext x
    simp only [a, b, c, d, RingHom.comp_apply, Localization.localRingHom_to_map]
    exact congrArg _ (targetClosureMap_commutes DAB DAC x)
  have : IsDomain DAB.A₁ :=
    (IsIntegralClosure.algebraMap_injective DAB.A₁ A K₁).isDomain
  have : IsDomain DAC.A₁ :=
    (IsIntegralClosure.algebraMap_injective DAC.A₁ A K₁).isDomain
  have ha : Function.Injective a := localRingHom_injective _
    (fun r hr => isNonZeroDivisor_algebraMap DAB r hr) _ _ _
  have hd : Function.Injective d := localRingHom_injective _
    (fun r hr => isNonZeroDivisor_algebraMap DAC r hr) _ _ _
  have : IsLocalHom a := Localization.isLocalHom_localRingHom _ _ _ _
  have : IsLocalHom b := Localization.isLocalHom_localRingHom _ _ _ _
  have : IsLocalHom d := Localization.isLocalHom_localRingHom _ _ _ _
  let := Localization.AtPrime.algebraOfLiesOver (q.under DAB.A₁) q
  let := Localization.AtPrime.algebraOfLiesOver (Q.under DAC.A₁) Q
  have hE1 : IsExtension (Localization.AtPrime (q.under DAB.A₁))
      (Localization.AtPrime q) :=
    { toFaithfulSMul := (faithfulSMul_iff_algebraMap_injective _ _).mpr ha
      toIsLocalHom := ‹IsLocalHom a› }
  have hE2 : IsExtension (Localization.AtPrime (Q.under DAC.A₁))
      (Localization.AtPrime Q) :=
    { toFaithfulSMul := (faithfulSMul_iff_algebraMap_injective _ _).mpr hd
      toIsLocalHom := ‹IsLocalHom d› }
  exact ⟨hd1, hv1, hd2, hv2, hd3, hv3, hd4, hv4, hE1, hE2,
    local_tower_descent _ _ _ _ a b c d hcbij ha hd hcomm⟩

private theorem descent_of_exists_lift
    {A : Type uA} {B : Type uB} {C : Type uC}
    {K : Type uK} {L : Type uL} {M : Type uM} {K₁ : Type uK₁}
    [CommRing A] [CommRing B] [CommRing C]
    [IsDomain A] [IsDomain B] [IsDomain C]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [IsDiscreteValuationRing C]
    [Field K] [Field L] [Field M] [Field K₁]
    [Algebra A B] [Algebra A C]
    [Algebra A K] [Algebra A L] [Algebra A M]
    [Algebra B L] [Algebra C M]
    [Algebra K L] [Algebra K M] [Algebra L M]
    [Algebra K K₁] [Algebra A K₁]
    [IsExtension A B]
    [IsExtension A C]
    [IsFractionRing A K] [IsFractionRing B L] [IsFractionRing C M]
    [IsScalarTower A B L]
    [IsScalarTower A C M]
    [IsScalarTower A K L] [IsScalarTower A K M] [IsScalarTower K L M]
    [IsScalarTower A K K₁] [Module.Finite K K₁]
    [Algebra B C] [Algebra B M] [IsScalarTower B C M] [IsScalarTower B L M]
    (DAB : IntegralClosureBaseChange.{uA, uB, uK, uL, uK₁, uL₁, uA₁, uB₁}
      A B K L K₁)
    (DAC : IntegralClosureBaseChange.{uA, uC, uK, uM, uK₁, uM₁, uA₂, uC₁}
      A C K M K₁)
    (hlift : ∀ q : Ideal DAB.B₁, q.IsMaximal →
      ∃ Q : Ideal DAC.B₁, Q.IsMaximal ∧ Q.comap (targetClosureMap DAB DAC) = q) :
    (DAC.IsWeakSolution → DAB.IsWeakSolution) ∧
      (DAC.IsSolution.{uA, uC, uK, uM, uK₁, uM₁, uA₂, uC₁, max uA₂ uC₁} →
        DAB.IsSolution.{uA, uB, uK, uL, uK₁, uL₁, uA₁, uB₁, max uA₁ uB₁}) := by
  refine ⟨fun h q hq => ?_, fun h q hq => ?_⟩ <;>
    obtain ⟨Q, hQ, hQq⟩ := hlift q hq <;> have := hq <;> have := hQ <;>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, h1, h2⟩ := localTower_descent DAB DAC q Q hQq
  · let := Localization.AtPrime.algebraOfLiesOver (q.under DAB.A₁) q
    let := Localization.AtPrime.algebraOfLiesOver (Q.under DAC.A₁) Q
    exact (ramificationIdx_eq_one_iff_isWeaklyUnramified q).mpr
      (h1 ((ramificationIdx_eq_one_iff_isWeaklyUnramified Q).mp (h Q hQ)))
  · exact h2 (h Q hQ)

private theorem ker_le_nilradical_of_injective_generic_fibre
    {R S T U : Type*} [CommRing R] [CommRing S] [CommRing T] [CommRing U]
    (g : R →+* S) (j : R →+* T) (q : T →+* U) (i : S →+* U)
    (hj : Function.Injective j) (hcomm : q.comp j = i.comp g)
    (hq : RingHom.ker q ≤ nilradical T) : RingHom.ker g ≤ nilradical R := by
  intro x hx
  have hqx : q (j x) = 0 := by
    simpa [RingHom.mem_ker.mp hx] using RingHom.congr_fun hcomm x
  exact mem_nilradical.mpr ((IsNilpotent.map_iff hj).mp (mem_nilradical.mp (hq hqx)))

private theorem ker_tensorMap_le_nilradical
    {R S T U : Type*} [CommRing R] [CommRing S] [CommRing T] [CommRing U]
    [Algebra R S] [Algebra R T] [Algebra R U]
    (f : S →ₐ[R] T) (hf : Function.Surjective f)
    (hk : RingHom.ker f.toRingHom ≤ nilradical S) :
    RingHom.ker (Algebra.TensorProduct.map f (AlgHom.id R U)).toRingHom ≤
      nilradical (S ⊗[R] U) := by
  change RingHom.ker (Algebra.TensorProduct.map f (AlgHom.id R U)) ≤ _
  rw [Algebra.TensorProduct.rTensor_ker (R := R) (C := U) f hf, Ideal.map_le_iff_le_comap]
  intro x hx
  exact mem_nilradical.mpr ((mem_nilradical.mp (hk hx)).map
    (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] U))

private theorem tensor_reduction_map
    {K L M E T U : Type*}
    [CommRing K] [CommRing L] [CommRing M] [CommRing E] [CommRing T] [CommRing U]
    [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
    [Algebra K E] [Algebra K T] [Algebra L T] [Algebra E T]
    [Algebra K U] [Algebra L U] [Algebra M U] [Algebra E U]
    [IsScalarTower K L T] [IsScalarTower K L U] [IsScalarTower L M U]
    (eT : T ≃ₐ[K] ((L ⊗[K] E) ⧸ nilradical (L ⊗[K] E)))
    (eU : U ≃ₐ[K] ((M ⊗[K] E) ⧸ nilradical (M ⊗[K] E)))
    (hTL : ∀ x : L, eT (algebraMap L T x) = Ideal.Quotient.mk _ (x ⊗ₜ[K] 1))
    (hTE : ∀ x : E, eT (algebraMap E T x) = Ideal.Quotient.mk _ (1 ⊗ₜ[K] x))
    (hUM : ∀ x : M, eU (algebraMap M U x) = Ideal.Quotient.mk _ (x ⊗ₜ[K] 1))
    (hUE : ∀ x : E, eU (algebraMap E U x) = Ideal.Quotient.mk _ (1 ⊗ₜ[K] x))
    (f : T →ₐ[L] U) (hfE : ∀ x : E, f (algebraMap E T x) = algebraMap E U x) :
    ∃ q : (M ⊗[L] T) →ₐ[M] U, Function.Surjective q ∧
      RingHom.ker q.toRingHom ≤ nilradical (M ⊗[L] T) ∧
      (∀ x : M, q (x ⊗ₜ[L] 1) = algebraMap M U x) ∧
      (∀ x : T, q (1 ⊗ₜ[L] x) = f x) := by
  let eTL : T ≃ₐ[L] ((L ⊗[K] E) ⧸ nilradical (L ⊗[K] E)) :=
    { eT.toRingEquiv with commutes' := hTL }
  let p : (L ⊗[K] E) →ₐ[L] T :=
    eTL.symm.toAlgHom.comp (Ideal.Quotient.mkₐ L _)
  have hp : Function.Surjective p := eTL.symm.surjective.comp Ideal.Quotient.mk_surjective
  have hpE (x : E) : p (1 ⊗ₜ[K] x) = algebraMap E T x :=
    eT.injective ((eTL.apply_symm_apply _).trans (hTE x).symm)
  let q := Algebra.TensorProduct.lift (Algebra.ofId M U) f (fun _ _ => Commute.all _ _)
  let c := Algebra.TensorProduct.cancelBaseChange K L L M E
  let s := (Algebra.TensorProduct.map (AlgHom.id L M) p).comp c.symm.toAlgHom
  have hs : Function.Surjective s :=
    (Algebra.TensorProduct.map_surjective _ _ Function.surjective_id hp).comp c.symm.surjective
  have hqs : q.toRingHom.comp s.toRingHom =
      eU.symm.toRingHom.comp (Ideal.Quotient.mk (nilradical (M ⊗[K] E))) := by
    apply Algebra.TensorProduct.ringHom_ext
    · ext x
      apply eU.injective
      simp [q, s, c, hUM, hpE]
    · ext x
      apply eU.injective
      simp [q, s, c, hpE, hfE, hUE]
  refine ⟨q, ?_, ?_, fun x => by simp [q], fun x => by simp [q]⟩
  · have : Function.Surjective (q.toRingHom.comp s.toRingHom) := by
      rw [hqs]
      exact eU.symm.surjective.comp Ideal.Quotient.mk_surjective
    intro y
    obtain ⟨x, hx⟩ := this y
    exact ⟨s x, hx⟩
  · intro x hx
    obtain ⟨y, rfl⟩ := hs x
    have hy : Ideal.Quotient.mk (nilradical (M ⊗[K] E)) y = 0 := by
      have h := RingHom.congr_fun hqs y
      change q (s y) = 0 at hx
      change q (s y) = eU.symm (Ideal.Quotient.mk _ y) at h
      rw [hx] at h
      exact eU.symm.injective (by simpa using h.symm)
    exact mem_nilradical.mpr ((mem_nilradical.mp
      (Ideal.Quotient.eq_zero_iff_mem.mp hy)).map s)

private theorem exists_maximal_over_integral_nilker
    {R S : Type*} [CommRing R] [CommRing S]
    (g : R →+* S) (hg : g.IsIntegral) (hk : RingHom.ker g ≤ nilradical R)
    (p : Ideal R) [p.IsMaximal] :
    ∃ q : Ideal S, q.IsMaximal ∧ q.comap g = p := by
  let : Algebra R S := g.toAlgebra
  have : Algebra.IsIntegral R S := (algebraMap_isIntegral_iff).mp hg
  exact Ideal.exists_ideal_over_maximal_of_isIntegral p (hk.trans (nilradical_le_prime p))

private theorem maximal_liesOver_composite_of_integral_nilker
    {R S T U : Type*} [CommRing R] [CommRing S] [CommRing T] [CommRing U]
    [Algebra R S] [Algebra R T] [Module.FaithfullyFlat R S]
    (g : (T ⊗[R] S) →+* U) (hg : g.IsIntegral)
    (hk : RingHom.ker g ≤ nilradical (T ⊗[R] S))
    (p : Ideal T) [hp : p.IsMaximal] :
    ∃ q : Ideal U, q.IsMaximal ∧ q.comap (g.comp (algebraMap T (T ⊗[R] S))) = p := by
  obtain ⟨P, hP⟩ := (PrimeSpectrum.comap_surjective_of_faithfullyFlat
    (A := T) (B := T ⊗[R] S)) ⟨p, hp.isPrime⟩
  have hPp : P.asIdeal.comap (algebraMap T (T ⊗[R] S)) = p :=
    congrArg PrimeSpectrum.asIdeal hP
  obtain ⟨Q, hQ, hPQ⟩ := Ideal.exists_le_maximal P.asIdeal P.isPrime.ne_top
  have hQp : Q.comap (algebraMap T (T ⊗[R] S)) = p :=
    (hp.eq_of_le (Ideal.comap_ne_top _ hQ.ne_top)
      (hPp.symm.le.trans (Ideal.comap_mono hPQ))).symm
  have := hQ
  obtain ⟨q, hq, heq⟩ := exists_maximal_over_integral_nilker g hg hk Q
  exact ⟨q, hq, by rw [← Ideal.comap_comap, heq, hQp]⟩

section Tower
variable
    (A : Type uA) (B : Type uB) (C : Type uC)
    (K : Type uK) (L : Type uL) (M : Type uM) (K₁ : Type uK₁)
    [CommRing A] [CommRing B] [CommRing C]
    [IsDomain A] [IsDomain B] [IsDomain C]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [IsDiscreteValuationRing C]
    [Field K] [Field L] [Field M] [Field K₁]
    [Algebra A B] [Algebra B C] [Algebra A C]
    [Algebra A K] [Algebra A L] [Algebra A M]
    [Algebra B L] [Algebra B M] [Algebra C M]
    [Algebra K L] [Algebra K M] [Algebra L M]
    [Algebra K K₁] [Algebra A K₁]
    [IsExtension A B] [IsExtension B C]
    [IsExtension A C]
    [IsFractionRing A K] [IsFractionRing B L] [IsFractionRing C M]
    [IsScalarTower A B C] [IsScalarTower A B L] [IsScalarTower A B M]
    [IsScalarTower B C M] [IsScalarTower A C M]
    [IsScalarTower A K L] [IsScalarTower A K M] [IsScalarTower K L M]
    [IsScalarTower B L M] [IsScalarTower A K K₁] [Module.Finite K K₁]
    (DAB : IntegralClosureBaseChange.{uA, uB, uK, uL, uK₁, uL₁, uA₁, uB₁}
      A B K L K₁)
    (DAC : IntegralClosureBaseChange.{uA, uC, uK, uM, uK₁, uM₁, uA₂, uC₁}
      A C K M K₁)

omit [Algebra B C] [Algebra B M] [IsExtension B C] [IsScalarTower A B C] [IsScalarTower A B M]
  [IsScalarTower B C M] [IsScalarTower B L M] in
private theorem reducedCompositumTensorMap :
    ∃ q : (M ⊗[L] DAB.L₁) →ₐ[M] DAC.L₁, Function.Surjective q ∧
      RingHom.ker q.toRingHom ≤ nilradical (M ⊗[L] DAB.L₁) ∧
      (∀ x, q (x ⊗ₜ[L] 1) = algebraMap M DAC.L₁ x) ∧
      (∀ x, q (1 ⊗ₜ[L] x) = reducedCompositumMap DAB DAC x) := by
  let : Algebra L DAC.L₁ := ((algebraMap M DAC.L₁).comp (algebraMap L M)).toAlgebra
  have : IsScalarTower L M DAC.L₁ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : IsScalarTower K L DAC.L₁ := IsScalarTower.of_algebraMap_eq (fun x => by
    rw [IsScalarTower.algebraMap_apply K M DAC.L₁,
      IsScalarTower.algebraMap_apply K L M]
    rfl)
  let f : DAB.L₁ →ₐ[L] DAC.L₁ :=
    { (reducedCompositumMap DAB DAC).toRingHom with
      commutes' := reducedCompositumMap_left DAB DAC }
  exact tensor_reduction_map DAB.eL₁ DAC.eL₁ DAB.eL₁_left DAB.eL₁_right
    DAC.eL₁_left DAC.eL₁_right f (reducedCompositumMap_right DAB DAC)

omit [IsExtension B C] [IsScalarTower A B C] [IsScalarTower A B M] in
private theorem targetClosureTensorIntegral :
    ∃ g : (DAB.B₁ ⊗[B] C) →+* DAC.B₁, g.IsIntegral ∧
      (∀ x, g (x ⊗ₜ[B] 1) = targetClosureMap DAB DAC x) ∧
      (∀ c, g (1 ⊗ₜ[B] c) = algebraMap C DAC.B₁ c) := by
  let : Algebra B DAC.B₁ := ((algebraMap C DAC.B₁).comp (algebraMap B C)).toAlgebra
  have : IsScalarTower B C DAC.B₁ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let f : DAB.B₁ →ₐ[B] DAC.B₁ :=
    { targetClosureMap DAB DAC with commutes' := targetClosureMap_base DAB DAC }
  let g := Algebra.TensorProduct.lift f (IsScalarTower.toAlgHom B C DAC.B₁)
    (fun _ _ => Commute.all _ _)
  have hgC : g.toRingHom.comp
      (Algebra.TensorProduct.includeRight : C →ₐ[B] DAB.B₁ ⊗[B] C).toRingHom =
      algebraMap C DAC.B₁ := by
    ext
    simp [g]
  have : Algebra.IsIntegral C DAC.B₁ := IsIntegralClosure.isIntegral_algebra C DAC.L₁
  refine ⟨g.toRingHom, ?_, fun x => by simp [g, f], fun c => by simp [g]⟩
  apply RingHom.IsIntegral.tower_top
    (Algebra.TensorProduct.includeRight : C →ₐ[B] DAB.B₁ ⊗[B] C).toRingHom
  rw [hgC]
  exact algebraMap_isIntegral_iff.mpr inferInstance

omit [IsScalarTower A B C] [IsScalarTower A B M] in
private theorem targetClosureTensor_ker_le_nilradical
    (g : (DAB.B₁ ⊗[B] C) →+* DAC.B₁)
    (hgleft : ∀ x, g (x ⊗ₜ[B] 1) = targetClosureMap DAB DAC x)
    (hgright : ∀ c, g (1 ⊗ₜ[B] c) = algebraMap C DAC.B₁ c) :
    RingHom.ker g ≤ nilradical (DAB.B₁ ⊗[B] C) := by
  obtain ⟨q, -, hq, hqM, hqT⟩ :=
    reducedCompositumTensorMap A B C K L M K₁ DAB DAC
  have : Module.IsTorsionFree B DAB.L₁ :=
    Module.IsTorsionFree.trans_faithfulSMul B L DAB.L₁
  let b := IsScalarTower.toAlgHom B DAB.B₁ DAB.L₁
  have : Module.IsTorsionFree B DAB.B₁ :=
    (IsIntegralClosure.algebraMap_injective DAB.B₁ B DAB.L₁).moduleIsTorsionFree b
      (fun r x => map_smul b r x)
  let a := IsScalarTower.toAlgHom B C M
  let t := Algebra.TensorProduct.map a b
  have ht : Function.Injective t := by
    change Function.Injective (TensorProduct.map a.toLinearMap b.toLinearMap)
    exact TensorProduct.map_injective_of_flat_flat_of_isDomain _ _
      (IsFractionRing.injective C M) (IsIntegralClosure.algebraMap_injective DAB.B₁ B DAB.L₁)
  let e := IsLocalization.algebraTensorEquiv (nonZeroDivisors B) L M DAB.L₁
  let j := e.symm.toRingHom.comp (t.toRingHom.comp (Algebra.TensorProduct.comm B DAB.B₁
    C).toRingHom)
  have hjtmul (x : DAB.B₁) (c : C) :
      j (x ⊗ₜ[B] c) = algebraMap C M c ⊗ₜ[L] algebraMap DAB.B₁ DAB.L₁ x := by
    simp [j, t, a, b, e, IsLocalization.algebraTensorEquiv,
      Algebra.TensorProduct.equivOfCompatibleSMul]
  have hj : Function.Injective j := e.symm.injective.comp
    (ht.comp (Algebra.TensorProduct.comm B DAB.B₁ C).injective)
  apply ker_le_nilradical_of_injective_generic_fibre g j q.toRingHom
    (algebraMap DAC.B₁ DAC.L₁) hj ?_ hq
  apply Algebra.TensorProduct.ringHom_ext
  · ext x
    change q (j (x ⊗ₜ[B] 1)) = algebraMap DAC.B₁ DAC.L₁ (g (x ⊗ₜ[B] 1))
    rw [hgleft, targetClosureMap_algebraMap, hjtmul, map_one]
    exact hqT _
  · ext x
    change q (j (1 ⊗ₜ[B] x)) = algebraMap DAC.B₁ DAC.L₁ (g (1 ⊗ₜ[B] x))
    rw [hgright, ← IsScalarTower.algebraMap_apply C DAC.B₁ DAC.L₁,
      IsScalarTower.algebraMap_apply C M DAC.L₁, hjtmul, map_one]
    exact hqM _

omit [IsScalarTower A B C] [IsScalarTower A B M] in
private theorem maximal_lift_for_descent :
    ∀ q : Ideal DAB.B₁, q.IsMaximal → ∃ Q : Ideal DAC.B₁,
      Q.IsMaximal ∧ Q.comap (targetClosureMap DAB DAC) = q := by
  intro q hq
  have := hq
  have : Module.FaithfullyFlat B C := Module.FaithfullyFlat.of_flat_of_isLocalHom
  obtain ⟨g, hg, hgleft, hgright⟩ := targetClosureTensorIntegral A B C K L M K₁ DAB DAC
  have hk := targetClosureTensor_ker_le_nilradical A B C K L M K₁ DAB DAC g hgleft hgright
  obtain ⟨Q, hQ, heq⟩ := maximal_liesOver_composite_of_integral_nilker g hg hk q
  have hcomp : g.comp (algebraMap DAB.B₁ (DAB.B₁ ⊗[B] C)) = targetClosureMap DAB DAC :=
    RingHom.ext hgleft
  exact ⟨Q, hQ, by simpa only [hcomp] using heq⟩

omit [IsScalarTower A B C] [IsScalarTower A B M] in
private theorem solutions_go_down :
    (DAC.IsWeakSolution → DAB.IsWeakSolution) ∧
      (DAC.IsSolution.{uA, uC, uK, uM, uK₁, uM₁, uA₂, uC₁, max uA₂ uC₁} →
        DAB.IsSolution.{uA, uB, uK, uL, uK₁, uL₁, uA₁, uB₁, max uA₁ uB₁}) :=
  descent_of_exists_lift DAB DAC (maximal_lift_for_descent A B C K L M K₁ DAB DAC)

end Tower

private theorem equiv_of_surjective_nilker
    {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C] [IsReduced B] [IsReduced C]
    (f : A →ₐ[R] B) (g : A →ₐ[R] C)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hkf : RingHom.ker f.toRingHom ≤ nilradical A)
    (hkg : RingHom.ker g.toRingHom ≤ nilradical A) :
    ∃ e : B ≃ₐ[R] C, ∀ x, e (f x) = g x := by
  have hfg : RingHom.ker f.toRingHom ≤ RingHom.ker g.toRingHom := fun x hx =>
    ((mem_nilradical.mp (hkf hx)).map g).eq_zero
  let h := AlgHom.liftOfSurjective f hf g hfg
  have hh : Function.Bijective h := by
    refine ⟨?_, AlgHom.liftOfSurjective_surjective f hf g hfg hg⟩
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, rfl⟩ := hf x
    have hy : g y = 0 := by simpa [h] using hx
    exact ((mem_nilradical.mp (hkg hy)).map f).eq_zero
  exact ⟨AlgEquiv.ofBijective h hh, AlgHom.liftOfSurjective_apply f hf g hfg⟩

private theorem tensor_product_reductions
    {L M T ι : Type*} [CommRing L] [CommRing M] [CommRing T] [Finite ι]
    [Algebra L M] [Algebra L T]
    (E U : ι → Type*) [∀ i, CommRing (E i)] [∀ i, CommRing (U i)]
    [∀ i, Algebra L (E i)] [∀ i, Algebra L (U i)] [∀ i, Algebra M (U i)]
    [∀ i, Algebra (E i) (U i)]
    (e : T ≃ₐ[L] ∀ i, E i)
    (d : ∀ i, U i ≃ₐ[L] ((M ⊗[L] E i) ⧸ nilradical (M ⊗[L] E i)))
    (hdM : ∀ i x, d i (algebraMap M (U i) x) = Ideal.Quotient.mk _ (x ⊗ₜ[L] 1))
    (hdE : ∀ i x, d i (algebraMap (E i) (U i) x) = Ideal.Quotient.mk _ (1 ⊗ₜ[L] x)) :
    ∃ r : (M ⊗[L] T) →ₐ[M] ∀ i, U i, Function.Surjective r ∧
      RingHom.ker r.toRingHom ≤ nilradical (M ⊗[L] T) ∧
      ∀ x i, r (1 ⊗ₜ[L] x) i = algebraMap (E i) (U i) (e x i) := by
  classical
  have := Fintype.ofFinite ι
  let dM (i : ι) : U i ≃ₐ[M] ((M ⊗[L] E i) ⧸ nilradical (M ⊗[L] E i)) :=
    { (d i).toRingEquiv with commutes' := hdM i }
  let p (i : ι) : (M ⊗[L] E i) →ₐ[M] U i :=
    (dM i).symm.toAlgHom.comp (Ideal.Quotient.mkₐ M _)
  have hp (i : ι) : Function.Surjective (p i) :=
    (dM i).symm.surjective.comp Ideal.Quotient.mk_surjective
  let c : (M ⊗[L] T) ≃ₐ[M] ∀ i, M ⊗[L] E i :=
    (Algebra.TensorProduct.congr (AlgEquiv.refl : M ≃ₐ[M] M) e).trans
      (Algebra.TensorProduct.piRight L M M E)
  let p' := AlgHom.pi (fun i => (p i).comp (Pi.evalAlgHom M _ i))
  have hp' : Function.Surjective p' := by
    intro x
    choose y hy using fun i => hp i (x i)
    exact ⟨y, funext hy⟩
  let r := p'.comp c.toAlgHom
  refine ⟨r, hp'.comp c.surjective, ?_, ?_⟩
  · intro x hx
    have hn : IsNilpotent (c x) := by
      refine (isNilpotent_pi_iff _).mpr fun i => ?_
      have hz : p i (c x i) = 0 := congrFun hx i
      have hz' : Ideal.Quotient.mk (nilradical (M ⊗[L] E i)) (c x i) = 0 := by
        apply (dM i).symm.injective
        simpa [p] using hz
      exact mem_nilradical.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz')
    exact mem_nilradical.mpr ((IsNilpotent.map_iff c.injective).mp hn)
  · intro x i
    apply (d i).injective
    change dM i (p i (c (1 ⊗ₜ[L] x) i)) = _
    simp [p, c, hdE]

private theorem integralClosure_product_equiv
    (R T A : Type*) [CommRing R] [CommRing T] [CommRing A]
    [Algebra R T] [Algebra R A] [Algebra A T] [IsScalarTower R A T]
    [IsIntegralClosure A R T]
    {ι : Type*} [Finite ι] (U V : ι → Type*) [∀ i, CommRing (U i)] [∀ i, CommRing (V i)]
    [∀ i, Algebra R (U i)] [∀ i, Algebra R (V i)] [∀ i, Algebra (V i) (U i)]
    [∀ i, IsScalarTower R (V i) (U i)] [∀ i, IsIntegralClosure (V i) R (U i)]
    (e : T ≃ₐ[R] ∀ i, U i) :
    ∃ d : A ≃ₐ[R] ∀ i, V i,
      ∀ x i, algebraMap (V i) (U i) (d x i) = e (algebraMap A T x) i := by
  let a := IsIntegralClosure.equiv R A T (integralClosure R T)
  let b : integralClosure R T ≃ₐ[R] integralClosure R (∀ i, U i) :=
    (e.subalgebraMap _).trans (Subalgebra.equivOfEq _ _ (integralClosure_map_algEquiv e))
  let c := integralClosurePiEquiv R U
  let d := AlgEquiv.piCongrRight (fun i =>
    IsIntegralClosure.equiv R (integralClosure R (U i)) (U i) (V i))
  refine ⟨a.trans (b.trans (c.trans d)), ?_⟩
  intro x i
  change algebraMap (V i) (U i)
    (IsIntegralClosure.equiv R (integralClosure R (U i)) (U i) (V i) (c (b (a x)) i)) = _
  rw [IsIntegralClosure.algebraMap_equiv]
  change (e ((a x).val)) i = _
  exact congrArg (fun t => e t i)
    (IsIntegralClosure.algebraMap_equiv R A T (integralClosure R T) x)

section Products
variable
    (A : Type uA) (B : Type uB) (C : Type uC)
    (K : Type uK) (L : Type uL) (M : Type uM) (K₁ : Type uK₁)
    [CommRing A] [CommRing B] [CommRing C]
    [IsDomain A] [IsDomain B] [IsDomain C]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [IsDiscreteValuationRing C]
    [Field K] [Field L] [Field M] [Field K₁]
    [Algebra A B] [Algebra B C] [Algebra A C]
    [Algebra A K] [Algebra A L] [Algebra A M]
    [Algebra B L] [Algebra B M] [Algebra C M]
    [Algebra K L] [Algebra K M] [Algebra L M]
    [Algebra K K₁] [Algebra A K₁]
    [IsExtension A B] [IsExtension B C]
    [IsExtension A C]
    [IsFractionRing A K] [IsFractionRing B L] [IsFractionRing C M]
    [IsScalarTower A B C] [IsScalarTower A B L] [IsScalarTower A B M]
    [IsScalarTower B C M] [IsScalarTower A C M]
    [IsScalarTower A K L] [IsScalarTower A K M] [IsScalarTower K L M]
    [IsScalarTower B L M] [IsScalarTower A K K₁] [Module.Finite K K₁]
    (DAB : IntegralClosureBaseChange.{uA, uB, uK, uL, uK₁, uL₁, uA₁, uB₁}
      A B K L K₁)
    (DAC : IntegralClosureBaseChange.{uA, uC, uK, uM, uK₁, uM₁, uA₂, uC₁}
      A C K M K₁)

variable {n : ℕ} (E : Fin n → Type uE)
    [∀ i, Field (E i)] [∀ i, Algebra L (E i)] [∀ i, Algebra B (E i)]
    [∀ i, IsScalarTower B L (E i)] [∀ i, Module.Finite L (E i)]
    (e : DAB.L₁ ≃ₐ[L] ∀ i, E i)
    (DBC : ∀ i, IntegralClosureBaseChange.{uB, uC, uL, uM, uE, uN₁, uB₂, uC₂}
      B C L M (E i))

omit [IsScalarTower A B C] [IsScalarTower A B M] in
private theorem product_normalization_compatible :
    ∃ d : DAC.L₁ ≃ₐ[M] ∀ i, (DBC i).L₁,
      ∀ x i, d (reducedCompositumMap DAB DAC x) i =
        algebraMap (E i) (DBC i).L₁ (e x i) := by
  obtain ⟨q, hqs, hq, -, hqT⟩ := reducedCompositumTensorMap A B C K L M K₁ DAB DAC
  obtain ⟨r, hrs, hr, hrT⟩ := tensor_product_reductions E (fun i => (DBC i).L₁) e
    (fun i => (DBC i).eL₁) (fun i => (DBC i).eL₁_left) (fun i => (DBC i).eL₁_right)
  have : IsReduced ((M ⊗[K] K₁) ⧸ nilradical (M ⊗[K] K₁)) :=
    (Ideal.isRadical_iff_quotient_reduced _).mp (Ideal.radical_isRadical _)
  have : IsReduced DAC.L₁ := isReduced_of_injective DAC.eL₁ DAC.eL₁.injective
  have : ∀ i, IsReduced (DBC i).L₁ := fun i => by
    have : IsReduced ((M ⊗[L] E i) ⧸ nilradical (M ⊗[L] E i)) :=
      (Ideal.isRadical_iff_quotient_reduced _).mp (Ideal.radical_isRadical _)
    exact isReduced_of_injective (DBC i).eL₁ (DBC i).eL₁.injective
  obtain ⟨d, hd⟩ := equiv_of_surjective_nilker q r hqs hrs hq hr
  exact ⟨d, fun x i => by rw [← hqT x, hd, hrT]⟩

include e in
omit [IsScalarTower A B C] [IsScalarTower A B M] in
private theorem product_integralClosures_compatible :
    ∃ a : DAB.B₁ ≃ₐ[B] ∀ i, (DBC i).A₁,
      ∃ b : DAC.B₁ ≃ₐ[C] ∀ i, (DBC i).B₁,
        ∀ x i, b (targetClosureMap DAB DAC x) i =
          algebraMap (DBC i).A₁ (DBC i).B₁ (a x i) := by
  obtain ⟨d, hd⟩ := product_normalization_compatible A B C K L M K₁ DAB DAC E e DBC
  obtain ⟨a, ha⟩ := integralClosure_product_equiv B DAB.L₁ DAB.B₁ E
    (fun i => (DBC i).A₁) (e.restrictScalars B)
  obtain ⟨b, hb⟩ := integralClosure_product_equiv C DAC.L₁ DAC.B₁
    (fun i => (DBC i).L₁) (fun i => (DBC i).B₁) (d.restrictScalars C)
  refine ⟨a, b, fun x i => ?_⟩
  apply IsIntegralClosure.algebraMap_injective (DBC i).B₁ C (DBC i).L₁
  change ∀ x i, algebraMap (DBC i).B₁ (DBC i).L₁ (b x i) =
    d (algebraMap DAC.B₁ DAC.L₁ x) i at hb
  change ∀ x i, algebraMap (DBC i).A₁ (E i) (a x i) =
    e (algebraMap DAB.B₁ DAB.L₁ x) i at ha
  rw [hb, targetClosureMap_algebraMap, hd, (DBC i).ringSquare, ha]

end Products

private theorem local_tower_composition
    (R : Type u) (R' : Type v) (S : Type w) (S' : Type t)
    (T : Type u₅) (T' : Type u₆)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [CommRing S'] [IsDomain S'] [IsDiscreteValuationRing S']
    [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [CommRing T'] [IsDomain T'] [IsDiscreteValuationRing T']
    (a : R →+* S) (b : S →+* T) (c : R →+* R') (d : R' →+* T)
    (e : S →+* S') (f : T →+* T') (g : S' →+* T')
    [IsLocalHom a] [IsLocalHom b] [IsLocalHom d] [IsLocalHom f] [IsLocalHom g]
    (hc : Function.Bijective c) (he : Function.Bijective e)
    (ha : Function.Injective a) (hd : Function.Injective d) (hg : Function.Injective g)
    (hcomm : b.comp a = d.comp c) (hcomm' : f.comp b = g.comp e) :
    letI := a.toAlgebra
    letI := d.toAlgebra
    letI := g.toAlgebra
    ∀ [IsExtension R S] [IsExtension R' T]
      [IsExtension S' T'],
    ((IsWeaklyUnramified R S ∧ IsWeaklyUnramified S' T') →
      IsWeaklyUnramified R' T) ∧
    ((RingHom.FormallySmoothNAdic.{max u w} a (IsLocalRing.maximalIdeal S) ∧
      RingHom.FormallySmoothNAdic.{max t u₆} g (IsLocalRing.maximalIdeal T')) →
      RingHom.FormallySmoothNAdic.{max v u₅} d (IsLocalRing.maximalIdeal T)) := by
  intro _ _ _
  have hb : Function.Injective b := by
    apply Function.Injective.of_comp (f := f)
    change Function.Injective (f.comp b)
    rw [hcomm']
    exact hg.comp he.1
  let := a.toAlgebra
  let := b.toAlgebra
  let := d.toAlgebra
  let := g.toAlgebra
  let : Algebra R T := (b.comp a).toAlgebra
  have : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : IsExtension S T :=
    { toFaithfulSMul := (faithfulSMul_iff_algebraMap_injective S T).mpr hb
      toIsLocalHom := ‹IsLocalHom b› }
  have : IsExtension R T :=
    { toFaithfulSMul := (faithfulSMul_iff_algebraMap_injective R T).mpr (hb.comp ha)
      toIsLocalHom := inferInstanceAs (IsLocalHom (b.comp a)) }
  have hST := local_tower_descent S S' T T' b f e g he hb hg hcomm'
  let c' := (RingEquiv.ofBijective c hc).symm.toRingHom
  have hcomm₂ : (RingHom.id T).comp d = (b.comp a).comp c' := by
    rw [hcomm, RingHom.comp_assoc]
    ext x
    exact congrArg d ((RingEquiv.ofBijective c hc).apply_symm_apply x).symm
  have hRT := local_tower_descent R' R T T d (RingHom.id T) c' (b.comp a)
    (RingEquiv.ofBijective c hc).symm.bijective hd (hb.comp ha) hcomm₂
  exact ⟨fun h => hRT.1 (isWeaklyUnramified_trans R S T h.1 (hST.1 h.2)),
    fun h => hRT.2 (formallySmoothNAdic_trans R S T h.1 (hST.2 h.2))⟩

/-- The localized maps of a commuting square of ring maps commute. -/
private theorem localRingHom_comp_eq {R S R' T : Type*} [CommRing R] [CommRing S] [CommRing R']
    [CommRing T] (f : R →+* S) (g : S →+* T) (a : R →+* R') (b : R' →+* T)
    (hcomm : g.comp f = b.comp a) (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]
    (p' : Ideal R') [p'.IsPrime] (Q : Ideal T) [Q.IsPrime] (hf : p = q.comap f)
    (hg : q = Q.comap g) (ha : p = p'.comap a) (hb : p' = Q.comap b) :
    (Localization.localRingHom q Q g hg).comp (Localization.localRingHom p q f hf) =
      (Localization.localRingHom p' Q b hb).comp (Localization.localRingHom p p' a ha) := by
  apply IsLocalization.ringHom_ext p.primeCompl
  ext x
  simp only [RingHom.comp_apply, Localization.localRingHom_to_map]
  exact congrArg _ (RingHom.congr_fun hcomm x)

private theorem localRingHom_eval_comp_equiv_bijective
    {R ι : Type*} [CommRing R] (S : ι → Type*) [∀ i, CommRing (S i)]
    (e : R ≃+* ∀ i, S i) (i : ι) (p : Ideal (S i)) [p.IsPrime] :
    let f := (Pi.evalRingHom S i).comp e.toRingHom
    Function.Bijective (Localization.localRingHom (p.comap f) p f rfl) := by
  intro f
  let P := p.comap (Pi.evalRingHom S i)
  let a := Localization.localRingEquiv (p.comap f) P e rfl
  have heq : Localization.localRingHom (p.comap f) p f rfl =
      (Localization.AtPrime.mapPiEvalRingHom p).comp a.toRingHom := by
    apply IsLocalization.ringHom_ext (p.comap f).primeCompl
    ext x
    change Localization.localRingHom (p.comap f) p f rfl (algebraMap R _ x) =
      Localization.localRingHom P p (Pi.evalRingHom S i) rfl
        (Localization.localRingHom (p.comap f) P e.toRingHom rfl (algebraMap R _ x))
    rw [Localization.localRingHom_to_map (p.comap f) P e.toRingHom rfl x,
      Localization.localRingHom_to_map P p (Pi.evalRingHom S i) rfl,
      Localization.localRingHom_to_map]
    rfl
  rw [heq]
  exact (Localization.AtPrime.mapPiEvalRingHom_bijective p).comp a.bijective

private theorem localizations_isExtension
    {A : Type uA} {B : Type uB} {K : Type uK} {L : Type uL} {K₁ : Type uK₁}
    [CommRing A] [CommRing B] [Field K] [Field L] [Field K₁]
    [IsDomain A] [IsDomain B] [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L]
    [Algebra K L] [Algebra K K₁] [Algebra A K₁]
    [IsExtension A B] [IsFractionRing A K] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsScalarTower A K K₁]
    [Module.Finite K K₁]
    (D : IntegralClosureBaseChange.{uA, uB, uK, uL, uK₁, uL₁, uA₁, uB₁} A B K L K₁)
    (q : Ideal D.B₁) (hq : q.IsMaximal) :
    letI : q.IsPrime := hq.isPrime
    letI := Localization.AtPrime.algebraOfLiesOver (q.under D.A₁) q
    ∃ (_ : IsDomain (Localization.AtPrime (q.under D.A₁)))
      (_ : IsDiscreteValuationRing (Localization.AtPrime (q.under D.A₁)))
      (_ : IsDomain (Localization.AtPrime q))
      (_ : IsDiscreteValuationRing (Localization.AtPrime q)),
      IsExtension (Localization.AtPrime (q.under D.A₁)) (Localization.AtPrime q) := by
  have : q.IsPrime := hq.isPrime
  have : Nontrivial D.B₁ := ⟨⟨0, 1, fun h =>
    hq.ne_top ((Ideal.eq_top_iff_one q).mpr (h ▸ q.zero_mem))⟩⟩
  have : Nontrivial D.L₁ :=
    (IsIntegralClosure.algebraMap_injective D.B₁ B D.L₁).nontrivial
  obtain ⟨-, hd, hv, hd', hv'⟩ := localizations_isDiscreteValuationRing D q hq
  have : IsDomain D.A₁ := (IsIntegralClosure.algebraMap_injective D.A₁ A K₁).isDomain
  let := Localization.AtPrime.algebraOfLiesOver (q.under D.A₁) q
  have hinj := localRingHom_injective (algebraMap D.A₁ D.B₁)
    (fun r hr => isNonZeroDivisor_algebraMap D r hr) (q.under D.A₁) q rfl
  exact ⟨hd, hv, hd', hv',
    { toFaithfulSMul := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
      toIsLocalHom := Localization.isLocalHom_localRingHom _ _ _ _ }⟩

private theorem exists_maximal_of_equiv_pi
    {R ι : Type*} [CommRing R] [Finite ι] (S : ι → Type*) [∀ i, CommRing (S i)]
    (e : R ≃+* ∀ i, S i) (Q : Ideal R) [hQ : Q.IsMaximal] :
    ∃ (i : ι) (p : Ideal (S i)), p.IsMaximal ∧
      Q = p.comap ((Pi.evalRingHom S i).comp e.toRingHom) := by
  classical
  obtain ⟨⟨i, p⟩, hp⟩ := (PrimeSpectrum.sigmaToPi_bijective S).surjective
    (PrimeSpectrum.comap e.symm.toRingHom ⟨Q, inferInstance⟩)
  let f : R →+* S i := (Pi.evalRingHom S i).comp e.toRingHom
  have hf : Function.Surjective f := fun x => ⟨e.symm (Pi.single i x), by simp [f]⟩
  have hQp : Q = p.asIdeal.comap f := by
    have he := congrArg (fun x : PrimeSpectrum (∀ i, S i) =>
      (PrimeSpectrum.comap e.toRingHom x).asIdeal) hp
    simpa [f, PrimeSpectrum.sigmaToPi_apply, Ideal.comap_comap] using he.symm
  have : (p.asIdeal.comap f).IsMaximal := hQp ▸ hQ
  have hm := Ideal.IsMaximal.map_of_surjective_of_ker_le hf
    (show RingHom.ker f ≤ p.asIdeal.comap f from Ideal.comap_mono bot_le)
  rw [Ideal.map_comap_of_surjective f hf] at hm
  exact ⟨i, p.asIdeal, hm, hQp⟩

section Composition
variable
    (A : Type uA) (B : Type uB) (C : Type uC)
    (K : Type uK) (L : Type uL) (M : Type uM) (K₁ : Type uK₁)
    [CommRing A] [CommRing B] [CommRing C]
    [IsDomain A] [IsDomain B] [IsDomain C]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [IsDiscreteValuationRing C]
    [Field K] [Field L] [Field M] [Field K₁]
    [Algebra A B] [Algebra B C] [Algebra A C]
    [Algebra A K] [Algebra A L] [Algebra A M]
    [Algebra B L] [Algebra B M] [Algebra C M]
    [Algebra K L] [Algebra K M] [Algebra L M]
    [Algebra K K₁] [Algebra A K₁]
    [IsExtension A B] [IsExtension B C]
    [IsExtension A C]
    [IsFractionRing A K] [IsFractionRing B L] [IsFractionRing C M]
    [IsScalarTower A B C] [IsScalarTower A B L] [IsScalarTower A B M]
    [IsScalarTower B C M] [IsScalarTower A C M]
    [IsScalarTower A K L] [IsScalarTower A K M] [IsScalarTower K L M]
    [IsScalarTower B L M] [IsScalarTower A K K₁] [Module.Finite K K₁]
    (DAB : IntegralClosureBaseChange.{uA, uB, uK, uL, uK₁, uL₁, uA₁, uB₁}
      A B K L K₁)
    (DAC : IntegralClosureBaseChange.{uA, uC, uK, uM, uK₁, uM₁, uA₂, uC₁}
      A C K M K₁)

variable {n : ℕ} (E : Fin n → Type uE)
    [∀ i, Field (E i)] [∀ i, Algebra L (E i)] [∀ i, Algebra B (E i)]
    [∀ i, IsScalarTower B L (E i)] [∀ i, Module.Finite L (E i)]
    (e : DAB.L₁ ≃ₐ[L] ∀ i, E i)
    (DBC : ∀ i, IntegralClosureBaseChange.{uB, uC, uL, uM, uE, uN₁, uB₂, uC₂}
      B C L M (E i))

include e in
omit [IsScalarTower A B C] [IsScalarTower A B M] in
private theorem solutions_compose :
    ((DAB.IsWeakSolution ∧ ∀ i, (DBC i).IsWeakSolution) → DAC.IsWeakSolution) ∧
    ((DAB.IsSolution.{uA, uB, uK, uL, uK₁, uL₁, uA₁, uB₁, max uA₁ uB₁} ∧
      ∀ i, (DBC i).IsSolution.{uB, uC, uL, uM, uE, uN₁, uB₂, uC₂, max uB₂ uC₂}) →
      DAC.IsSolution.{uA, uC, uK, uM, uK₁, uM₁, uA₂, uC₁, max uA₂ uC₁}) := by
  classical
  obtain ⟨eB, eC, hsquare⟩ := product_integralClosures_compatible A B C K L M K₁ DAB DAC E e DBC
  have hlocal (Q : Ideal DAC.B₁) (hQ : Q.IsMaximal) :
      let : Q.IsPrime := hQ.isPrime
      ((DAB.IsWeakSolution ∧ ∀ i, (DBC i).IsWeakSolution) → Q.ramificationIdx DAC.A₁ = 1) ∧
      ((DAB.IsSolution.{uA, uB, uK, uL, uK₁, uL₁, uA₁, uB₁, max uA₁ uB₁} ∧
        ∀ i, (DBC i).IsSolution.{uB, uC, uL, uM, uE, uN₁, uB₂, uC₂, max uB₂ uC₂}) →
        RingHom.FormallySmoothNAdic.{max uA₂ uC₁}
          (Localization.localRingHom (Q.under DAC.A₁) Q (algebraMap DAC.A₁ DAC.B₁) rfl)
          (IsLocalRing.maximalIdeal (Localization.AtPrime Q))) := by
    have := hQ
    obtain ⟨i, Qi, hQi, hQeq⟩ := exists_maximal_of_equiv_pi
      (fun i => (DBC i).B₁) eC.toRingEquiv Q
    have := hQi
    let u := (Pi.evalRingHom (fun j => (DBC j).A₁) i).comp eB.toRingHom
    let v := (Pi.evalRingHom (fun j => (DBC j).B₁) i).comp eC.toRingHom
    change Q = Qi.comap v at hQeq
    let qi := Qi.under (DBC i).A₁
    have hqi : qi.IsMaximal := (localizations_isDiscreteValuationRing (DBC i) Qi hQi).1
    have := hqi
    let q := qi.comap u
    have hu : Function.Surjective u := fun x => ⟨eB.symm (Pi.single i x), by simp [u]⟩
    have hq : q.IsMaximal := Ideal.comap_isMaximal_of_surjective u hu
    have := hq
    let f₀ := targetClosureMap DAB DAC
    have hsquare' : v.comp f₀ = (algebraMap (DBC i).A₁ (DBC i).B₁).comp u :=
      RingHom.ext (fun x => hsquare x i)
    have hQq : Q.comap f₀ = q := by
      rw [hQeq, Ideal.comap_comap, hsquare']
      rfl
    let := Localization.AtPrime.algebraOfLiesOver (q.under DAB.A₁) q
    let := Localization.AtPrime.algebraOfLiesOver (Q.under DAC.A₁) Q
    let := Localization.AtPrime.algebraOfLiesOver qi Qi
    obtain ⟨_, _, _, _, hAB⟩ := localizations_isExtension DAB q hq
    obtain ⟨_, _, _, _, hAC⟩ := localizations_isExtension DAC Q hQ
    obtain ⟨_, _, _, _, hBC⟩ := localizations_isExtension (DBC i) Qi hQi
    let eb := baseClosureEquiv DAB DAC
    have hbase : f₀.comp (algebraMap DAB.A₁ DAB.B₁) =
        (algebraMap DAC.A₁ DAC.B₁).comp eb.toRingHom :=
      RingHom.ext (targetClosureMap_commutes DAB DAC)
    have hp : q.under DAB.A₁ = (Q.under DAC.A₁).comap eb.toRingHom := by
      change _ = Ideal.comap _ (Ideal.comap _ Q)
      rw [Ideal.comap_comap, ← hbase, ← Ideal.comap_comap, hQq]
    let a := Localization.localRingHom (q.under DAB.A₁) q (algebraMap DAB.A₁ DAB.B₁) rfl
    let b := Localization.localRingHom q Q f₀ hQq.symm
    let c := Localization.localRingHom (q.under DAB.A₁) (Q.under DAC.A₁) eb.toRingHom hp
    let d := Localization.localRingHom (Q.under DAC.A₁) Q (algebraMap DAC.A₁ DAC.B₁) rfl
    let u' := Localization.localRingHom q qi u rfl
    let v' := Localization.localRingHom Q Qi v hQeq
    let g := Localization.localRingHom qi Qi (algebraMap (DBC i).A₁ (DBC i).B₁) rfl
    have hc : Function.Bijective c :=
      (Localization.localRingEquiv (q.under DAB.A₁) (Q.under DAC.A₁) eb.toRingEquiv hp).bijective
    have hu' : Function.Bijective u' :=
      localRingHom_eval_comp_equiv_bijective (fun j => (DBC j).A₁) eB.toRingEquiv i qi
    have ha : Function.Injective a := FaithfulSMul.algebraMap_injective _ _
    have hd : Function.Injective d := FaithfulSMul.algebraMap_injective _ _
    have hg : Function.Injective g := FaithfulSMul.algebraMap_injective _ _
    have hcomm : b.comp a = d.comp c :=
      localRingHom_comp_eq _ _ _ _ hbase _ _ _ _ rfl hQq.symm hp rfl
    have hcomm' : v'.comp b = g.comp u' :=
      localRingHom_comp_eq _ _ _ _ hsquare' _ _ _ _ hQq.symm hQeq rfl rfl
    obtain ⟨hw, hs⟩ := local_tower_composition _ _ _ _ _ _ a b c d u' v' g
      hc hu' ha hd hg hcomm hcomm'
    exact ⟨fun h => (ramificationIdx_eq_one_iff_isWeaklyUnramified Q).mpr
        (hw ⟨(ramificationIdx_eq_one_iff_isWeaklyUnramified q).mp (h.1 q hq),
          (ramificationIdx_eq_one_iff_isWeaklyUnramified Qi).mp (h.2 i Qi hQi)⟩),
      fun h => hs ⟨h.1 q hq, h.2 i Qi hQi⟩⟩
  exact ⟨fun h Q hQ => (hlocal Q hQ).1 h, fun h Q hQ => (hlocal Q hQ).2 h⟩

end Composition

/-- Weak solutions and solutions descend along a tower of extensions of discrete valuation
rings. Conversely, they compose provided every field factor of the intermediate reduced tensor
product is respectively a weak solution or a solution for the upper extension. -/
@[stacks 09ES]
theorem weakSolutions_and_solutions_go_down_and_compose
    (A : Type uA) (B : Type uB) (C : Type uC)
    (K : Type uK) (L : Type uL) (M : Type uM) (K₁ : Type uK₁)
    [CommRing A] [CommRing B] [CommRing C]
    [IsDomain A] [IsDomain B] [IsDomain C]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [IsDiscreteValuationRing C]
    [Field K] [Field L] [Field M] [Field K₁]
    [Algebra A B] [Algebra B C] [Algebra A C]
    [Algebra A K] [Algebra A L] [Algebra A M]
    [Algebra B L] [Algebra B M] [Algebra C M]
    [Algebra K L] [Algebra K M] [Algebra L M]
    [Algebra K K₁] [Algebra A K₁]
    [IsExtension A B] [IsExtension B C]
    [IsExtension A C]
    [IsFractionRing A K] [IsFractionRing B L] [IsFractionRing C M]
    [IsScalarTower A B C] [IsScalarTower A B L] [IsScalarTower A B M]
    [IsScalarTower B C M] [IsScalarTower A C M]
    [IsScalarTower A K L] [IsScalarTower A K M] [IsScalarTower K L M]
    [IsScalarTower B L M] [IsScalarTower A K K₁] [Module.Finite K K₁]
    (DAB : IntegralClosureBaseChange.{uA, uB, uK, uL, uK₁, uL₁, uA₁, uB₁}
      A B K L K₁)
    (DAC : IntegralClosureBaseChange.{uA, uC, uK, uM, uK₁, uM₁, uA₂, uC₁}
      A C K M K₁) :
    letI := DAB.commRingL₁
    letI := DAB.algebraLL₁
    ((DAC.IsWeakSolution → DAB.IsWeakSolution) ∧
      (DAC.IsSolution.{uA, uC, uK, uM, uK₁, uM₁, uA₂, uC₁, max uA₂ uC₁} →
        DAB.IsSolution.{uA, uB, uK, uL, uK₁, uL₁, uA₁, uB₁, max uA₁ uB₁})) ∧
      ∀ (n : ℕ) (E : Fin n → Type uE)
        [∀ i, Field (E i)] [∀ i, Algebra L (E i)] [∀ i, Algebra B (E i)]
        [∀ i, IsScalarTower B L (E i)] [∀ i, Module.Finite L (E i)],
        0 < n → Nonempty (DAB.L₁ ≃ₐ[L] ∀ i, E i) →
          ∀ DBC : ∀ i, IntegralClosureBaseChange.{uB, uC, uL, uM, uE, uN₁, uB₂, uC₂}
              B C L M (E i),
            ((DAB.IsWeakSolution ∧ ∀ i, (DBC i).IsWeakSolution) →
              DAC.IsWeakSolution) ∧
            ((DAB.IsSolution.{uA, uB, uK, uL, uK₁, uL₁, uA₁, uB₁, max uA₁ uB₁} ∧
                ∀ i, (DBC i).IsSolution.{uB, uC, uL, uM, uE, uN₁, uB₂, uC₂, max uB₂ uC₂}) →
              DAC.IsSolution.{uA, uC, uK, uM, uK₁, uM₁, uA₂, uC₁, max uA₂ uC₁}) := by
  let := DAB.commRingL₁
  let := DAB.algebraLL₁
  refine ⟨solutions_go_down A B C K L M K₁ DAB DAC, ?_⟩
  intro n E _ _ _ _ _ _hn he DBC
  obtain ⟨e⟩ := he
  exact solutions_compose A B C K L M K₁ DAB DAC E e DBC

end

end IsDiscreteValuationRing
