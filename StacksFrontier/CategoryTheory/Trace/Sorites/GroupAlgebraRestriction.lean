module

public import Mathlib.Algebra.DirectSum.Finsupp
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.GroupTheory.Coset.Basic
public import Mathlib.LinearAlgebra.StdBasis

/-!
# Restricting scalars along the inclusion of a subgroup algebra

Let `Λ` be a ring, `G` a finite group and `H` a subgroup of `G`.  Choosing a system of
representatives for the orbits of left multiplication by `H` exhibits `Λ[G]` as a direct
summand of a free `Λ[H]`-module, so `Λ[G]` is projective over `Λ[H]`.  Projectivity then
descends along the tower `Λ[H] ⊆ Λ[G]`: a module projective over `Λ[G]` stays projective
after restricting scalars to `Λ[H]`.

## Main definitions

* `MonoidAlgebra.subgroupCoeff` collects the coefficients of an element of `Λ[G]` along the
  left `H`-orbit of a group element, as an element of `Λ[H]`.

## Main results

* `Module.Projective.finsupp`: finitely supported functions into a projective module form a
  projective module.
* `Module.Projective.trans_of_isScalarTower`: projectivity descends along a tower of rings
  whose larger ring is projective over the smaller.  Unlike `Module.Projective.trans` this
  needs no commutativity and no algebra structure, only a scalar tower.
* `MonoidAlgebra.projective_restrictScalars_subgroup`: the group algebra of a finite group is
  projective over the group algebra of a subgroup.
-/

@[expose] public section

open scoped MonoidAlgebra

namespace Module.Projective

variable (R S : Type*) [Semiring R] [Semiring S] [Module R S]

/-- Finitely supported functions into a projective module form a projective module. -/
theorem finsupp (ι : Type*) [Module.Projective R S] : Module.Projective R (ι →₀ S) := by
  classical
  have : Module.Projective R (DirectSum ι fun _ : ι => S) :=
    Module.Projective.directSum_iff.2 fun _ => inferInstance
  exact Module.Projective.of_equiv' (finsuppLEquivDirectSum R S ι).symm

/-- Projectivity descends along a tower of rings: if `M` is projective over `S` and `S` is
projective over `R`, then `M` is projective over `R`. -/
theorem trans_of_isScalarTower (M : Type*) [AddCommMonoid M] [Module S M] [Module R M]
    [IsScalarTower R S S] [IsScalarTower R S M]
    [Module.Projective S M] [Module.Projective R S] : Module.Projective R M := by
  obtain ⟨s, hs⟩ := ‹Module.Projective S M›
  have : Module.Projective R (M →₀ S) := finsupp R S M
  exact Module.Projective.of_split (LinearMap.restrictScalars R s)
    (LinearMap.restrictScalars R (Finsupp.linearCombination S (id : M → M)))
    (LinearMap.ext fun m => hs m)

end Module.Projective

namespace Subgroup

variable {G : Type*} [Group G] (H : Subgroup G)

/-- A group is the product of a subgroup and a system of representatives for the orbits of
left multiplication by that subgroup. -/
noncomputable def leftCosetProductEquiv :
    G ≃ H × Quotient (QuotientGroup.rightRel H) := by
  classical
  refine
    { toFun := fun g => ⟨⟨g * (Quotient.out (Quotient.mk (QuotientGroup.rightRel H) g))⁻¹, ?_⟩,
        Quotient.mk (QuotientGroup.rightRel H) g⟩
      invFun := fun x => (x.1 : G) * Quotient.out x.2
      left_inv := ?_
      right_inv := ?_ }
  · have hq : Quotient.mk (QuotientGroup.rightRel H)
        (Quotient.out (Quotient.mk (QuotientGroup.rightRel H) g)) =
        Quotient.mk (QuotientGroup.rightRel H) g := Quotient.out_eq' _
    simpa only [QuotientGroup.rightRel_apply] using Quotient.exact' hq
  · intro g
    simp
  · rintro ⟨h, q⟩
    have hm : Quotient.mk (QuotientGroup.rightRel H) ((h : G) * Quotient.out q) = q := by
      rw [← Quotient.out_eq' q]
      apply Quotient.sound'
      rw [QuotientGroup.rightRel_apply]
      simp
    have hrep : Quotient.out (Quotient.mk (QuotientGroup.rightRel H)
        ((h : G) * Quotient.out q)) = Quotient.out q := congrArg Quotient.out hm
    refine Prod.ext (Subtype.ext ?_) hm
    change ((h : G) * Quotient.out q) * (Quotient.out (Quotient.mk
      (QuotientGroup.rightRel H) ((h : G) * Quotient.out q)))⁻¹ = (h : G)
    rw [hrep]
    simp

/-- Summing over a subgroup and over representatives of the orbits of left multiplication by
it is the same as summing over the whole group. -/
theorem sum_coset_representatives [Fintype G] [Fintype H]
    [Fintype (Quotient (QuotientGroup.rightRel H))] {A : Type*} [AddCommMonoid A] (f : G → A) :
    (∑ q : Quotient (QuotientGroup.rightRel H), ∑ h : H,
      f ((h : G) * Quotient.out q)) = ∑ g, f g := by
  rw [Finset.sum_comm]
  exact (Fintype.sum_prod_type (fun z : H × Quotient (QuotientGroup.rightRel H) =>
    f ((z.1 : G) * Quotient.out z.2))).symm.trans
      (Equiv.sum_comp (leftCosetProductEquiv H).symm f)

end Subgroup

namespace MonoidAlgebra

/-- An element of a group algebra over a finite monoid is the sum of its monomials. -/
theorem eq_sum_single_coeff (Λ : Type*) [Ring Λ] (G : Type*) [Monoid G] [Fintype G]
    (a : Λ[G]) : a = ∑ g, single g (a.coeff g) := by
  classical
  ext g
  simp

variable (Λ : Type*) [Ring Λ] {G : Type*} [Group G] (H : Subgroup G)

/-- The map `Λ[H] → Λ[G]` induced by the inclusion `H → G` commutes with scalar multiplication by
`Λ`. -/
theorem mapDomainRingHom_smul (r : Λ) (b : Λ[H]) :
    mapDomainRingHom Λ H.subtype (r • b) = r • mapDomainRingHom Λ H.subtype b := by
  ext g
  simp [mapDomainRingHom]

section

variable [Fintype H]

/-- The coefficients of an element of `Λ[G]` along the left `H`-orbit of `k`, assembled into
an element of `Λ[H]`. -/
noncomputable def subgroupCoeff (k : G) (a : Λ[G]) : Λ[H] :=
  ∑ h : H, single h (a.coeff ((h : G) * k))

/-- The coefficient of `subgroupCoeff Λ H k a` at `h` is the coefficient of `a` at `h * k`. -/
@[simp]
theorem coeff_subgroupCoeff (k : G) (a : Λ[G]) (h : H) :
    (subgroupCoeff Λ H k a).coeff h = a.coeff ((h : G) * k) := by
  classical
  rw [subgroupCoeff, MonoidAlgebra.coeff_sum]
  simp [Finsupp.single_apply]

/-- `subgroupCoeff Λ H k` is additive. -/
theorem subgroupCoeff_add (k : G) (a b : Λ[G]) :
    subgroupCoeff Λ H k (a + b) = subgroupCoeff Λ H k a + subgroupCoeff Λ H k b := by
  ext h
  simp

/-- `subgroupCoeff Λ H k` commutes with scalar multiplication by `Λ`. -/
theorem subgroupCoeff_smul (k : G) (r : Λ) (a : Λ[G]) :
    subgroupCoeff Λ H k (r • a) = r • subgroupCoeff Λ H k a := by
  ext h
  simp

/-- The image of `subgroupCoeff Λ H k a` in `Λ[G]` is `∑ h : H, single h (a.coeff (h * k))`. -/
theorem mapDomainRingHom_subgroupCoeff (k : G) (a : Λ[G]) :
    mapDomainRingHom Λ H.subtype (subgroupCoeff Λ H k a) =
      ∑ h : H, single (h : G) (a.coeff ((h : G) * k)) := by
  simp [subgroupCoeff, map_sum, mapDomainRingHom]

/-- The orbit coefficients are linear over the subgroup algebra. -/
theorem subgroupCoeff_mul (k : G) (b : Λ[H]) (a : Λ[G]) :
    subgroupCoeff Λ H k (mapDomainRingHom Λ H.subtype b * a) =
      b * subgroupCoeff Λ H k a := by
  classical
  induction b using MonoidAlgebra.induction_on with
  | of h₀ =>
      ext h
      rw [MonoidAlgebra.of_apply, show mapDomainRingHom Λ H.subtype (single h₀ (1 : Λ)) =
        single (h₀ : G) (1 : Λ) from mapDomain_single]
      simp only [coeff_subgroupCoeff, coeff_single_mul_apply, one_mul,
        Subgroup.coe_mul, Subgroup.coe_inv]
      rw [mul_assoc]
  | add b c hb hc => rw [map_add, add_mul, subgroupCoeff_add, hb, hc, add_mul]
  | smul r b hb =>
      rw [mapDomainRingHom_smul, smul_mul_assoc, subgroupCoeff_smul, hb, smul_mul_assoc]

end

/-- The group algebra of a finite group is projective as a module over the group algebra of a
subgroup, the module structure being restriction of scalars along the inclusion. -/
theorem projective_restrictScalars_subgroup [Finite G] :
    letI : Module Λ[H] Λ[G] := Module.compHom _ (mapDomainRingHom Λ H.subtype)
    Module.Projective Λ[H] Λ[G] := by
  classical
  let : Module Λ[H] Λ[G] := Module.compHom _ (mapDomainRingHom Λ H.subtype)
  let : Fintype G := Fintype.ofFinite G
  let : Fintype H := Fintype.ofFinite H
  let : Fintype (Quotient (QuotientGroup.rightRel H)) :=
    Quotient.fintype (QuotientGroup.rightRel H)
  have hsmul : ∀ (b : Λ[H]) (x : Λ[G]), b • x = mapDomainRingHom Λ H.subtype b * x :=
    fun _ _ => rfl
  let i : Λ[G] →ₗ[Λ[H]] (Quotient (QuotientGroup.rightRel H) → Λ[H]) :=
    { toFun := fun a q => subgroupCoeff Λ H (Quotient.out q) a
      map_add' := fun a b => funext fun q => subgroupCoeff_add Λ H _ a b
      map_smul' := fun b a => funext fun q => by
        show subgroupCoeff Λ H (Quotient.out q) (b • a) = b * subgroupCoeff Λ H _ a
        rw [hsmul]
        exact subgroupCoeff_mul Λ H _ b a }
  let s : (Quotient (QuotientGroup.rightRel H) → Λ[H]) →ₗ[Λ[H]] Λ[G] :=
    { toFun := fun x => ∑ q, mapDomainRingHom Λ H.subtype (x q) * single (Quotient.out q) 1
      map_add' := fun x y => by
        simp only [Pi.add_apply, map_add, add_mul]
        exact Finset.sum_add_distrib
      map_smul' := fun b x => by
        show (∑ q, mapDomainRingHom Λ H.subtype (b * x q) * single (Quotient.out q) 1) =
          mapDomainRingHom Λ H.subtype b *
            ∑ q, mapDomainRingHom Λ H.subtype (x q) * single (Quotient.out q) 1
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun q _ => by rw [map_mul, mul_assoc] }
  refine Module.Projective.of_split i s (LinearMap.ext fun a => ?_)
  show (∑ q, mapDomainRingHom Λ H.subtype (subgroupCoeff Λ H (Quotient.out q) a) *
    single (Quotient.out q) 1) = a
  calc
    _ = ∑ q : Quotient (QuotientGroup.rightRel H), ∑ h : H,
        single ((h : G) * Quotient.out q) (a.coeff ((h : G) * Quotient.out q)) := by
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [mapDomainRingHom_subgroupCoeff, Finset.sum_mul]
      exact Finset.sum_congr rfl fun h _ => by rw [single_mul_single, mul_one]
    _ = ∑ g : G, single g (a.coeff g) :=
      Subgroup.sum_coset_representatives H fun g => single g (a.coeff g)
    _ = a := (eq_sum_single_coeff Λ G a).symm

end MonoidAlgebra
