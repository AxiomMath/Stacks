module

public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.RingTheory.AdicCompletion.RingHom
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import StacksFrontier.Deformation.Basic
public import StacksFrontier.Deformation.Completed.Basic
public import StacksFrontier.Deformation.FormalObject.Basic
public import StacksFrontier.Deformation.FormalObject.Unit
public import StacksFrontier.Deformation.Groupoid.BaseCategory
public import StacksFrontier.Deformation.Predeformation.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Completion of representable and limit-preserving functors

Completion of a restricted representable functor, and of a functor
preserving the relevant limits.

## Main definitions

* `AdicSection` is a compatible family of values on the Artinian quotients of
  a complete local algebra.
* `adicCompletion` sends a functor on Artinian local algebras to the functor of
  its adic sections on complete local algebras.

## Main results

* `coyonedaIsoAdicCompletion` is the canonical natural isomorphism for a
  representable functor.
* `coyonedaIsoAdicCompletion_hom_apply` specifies its forward map on every
  component and every adic quotient.
* `adicCompletionRestrictionIso` is the canonical natural isomorphism.
* `adicCompletionRestrictionIso_hom_apply` describes its map on every adic quotient.

## Implementation notes

### Completion of a restricted representable functor

The completion is expressed by the inverse limit over the positive powers
`m_S ^ (n + 1)`. Its elements are compatible families; the functorial action
uses the quotient maps induced by a morphism of complete local algebras.
The canonical isomorphism, rather than a mere pointwise bijection, records
naturality in the complete local algebra. Its forward map sends `f : R ⟶ S`
to the family of composites with the quotient maps `S → S / m_S ^ (n + 1)`;
this also determines its inverse uniquely.

### Completion of a limit-preserving functor

The functor completion and inclusion of Artinian algebras are those already
defined for the representable case. The component formula specifies the
canonical isomorphism: a value on a complete algebra is sent to its images
on all positive maximal-ideal quotients.

## References

* [Stacks Project, Tag 06HE](https://stacks.math.columbia.edu/tag/06HE)
-/

@[expose] public section

namespace Deformation

/-! ### Completion of a restricted representable functor -/

section
open CategoryTheory
open IsLocalRing
universe u v w


variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- A compatible family of values of a functor on the Artinian quotients of `S`. -/
public structure AdicSection (F : ArtinianLocalAlgCat.{u, v, w} Λ k ⥤ Type v)
    (S : CompleteLocalAlgCat.{u, v, w} Λ k) where
  value : (n : ℕ) → F.obj (AdicTruncation.obj S n)
  compatible : ∀ n,
    F.map (AdicTruncation.transition S n) (value (n + 1)) = value n

namespace AdicSection

/-- Push a compatible family forward along a morphism of complete local algebras. -/
public noncomputable def map {F : ArtinianLocalAlgCat.{u, v, w} Λ k ⥤ Type v}
    {S T : CompleteLocalAlgCat.{u, v, w} Λ k} (f : S ⟶ T)
    (x : AdicSection F S) : AdicSection F T where
  value n := F.map (AdicTruncation.map f n) (x.value n)
  compatible n := by
    calc
      F.map (AdicTruncation.transition T n)
          (F.map (AdicTruncation.map f (n + 1)) (x.value (n + 1))) =
          F.map (AdicTruncation.map f (n + 1) ≫
            AdicTruncation.transition T n) (x.value (n + 1)) := by
              rw [F.map_comp]
              rfl
      _ = F.map (AdicTruncation.transition S n ≫
            AdicTruncation.map f n) (x.value (n + 1)) := by
              have hnat := (AdicTruncation.transitionNat n).naturality f
              change AdicTruncation.map f (n + 1) ≫
                AdicTruncation.transition T n =
                AdicTruncation.transition S n ≫ AdicTruncation.map f n at hnat
              rw [hnat]
      _ = F.map (AdicTruncation.map f n)
            (F.map (AdicTruncation.transition S n) (x.value (n + 1))) := by
              rw [F.map_comp]
              rfl
      _ = F.map (AdicTruncation.map f n) (x.value n) := by
            rw [x.compatible n]

/-- Two compatible families are equal if their values agree at every level. -/
@[ext]
public theorem ext {F : ArtinianLocalAlgCat.{u, v, w} Λ k ⥤ Type v}
    {S : CompleteLocalAlgCat.{u, v, w} Λ k} {x y : AdicSection F S}
    (h : ∀ n, x.value n = y.value n) : x = y := by
  cases x
  cases y
  congr
  exact funext h

end AdicSection

/-- The adic completion of a functor on Artinian local algebras, evaluated by
compatible families on all maximal-ideal quotients. -/
public noncomputable def adicCompletion (F : ArtinianLocalAlgCat.{u, v, w} Λ k ⥤ Type v) :
    CompleteLocalAlgCat.{u, v, w} Λ k ⥤ Type v where
  obj S := AdicSection F S
  map f := TypeCat.ofHom (AdicSection.map (F := F) f)
  map_id S := by
    apply TypeCat.homEquiv.injective
    funext x
    apply AdicSection.ext
    intro n
    change F.map (AdicTruncation.map (𝟙 S) n) (x.value n) = x.value n
    have h : AdicTruncation.map (𝟙 S) n = 𝟙 (AdicTruncation.obj S n) :=
      (AdicTruncation.functor n).map_id S
    rw [h, F.map_id]
    rfl
  map_comp f g := by
    apply TypeCat.homEquiv.injective
    funext x
    apply AdicSection.ext
    intro n
    change F.map (AdicTruncation.map (f ≫ g) n) (x.value n) =
      F.map (AdicTruncation.map g n)
        (F.map (AdicTruncation.map f n) (x.value n))
    have h : AdicTruncation.map (f ≫ g) n =
        AdicTruncation.map f n ≫ AdicTruncation.map g n :=
      (AdicTruncation.functor n).map_comp f g
    rw [h, F.map_comp]
    rfl

/-- The quotient map from a complete local algebra onto its `n`-th adic truncation,
as a morphism of complete local algebras. -/
noncomputable def quotientProjection (S : CompleteLocalAlgCat.{u, v, w} Λ k)
    (n : ℕ) : S ⟶ artinianToComplete.obj (AdicTruncation.obj S n) := by
  let I := AdicTruncation.ideal S n
  letI : Nontrivial (S ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr
    ((Ideal.pow_le_self (Nat.succ_ne_zero n)).trans_lt (maximalIdeal.isMaximal S).lt_top).ne
  letI : IsLocalRing (S ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let q := Ideal.Quotient.mkₐ Λ I
  refine ⟨q, IsLocalHom.of_surjective q.toRingHom Ideal.Quotient.mk_surjective, ?_⟩
  intro a
  change AdicTruncation.residueEquiv S n
    (residue (S ⧸ AdicTruncation.ideal S n)
      (Ideal.Quotient.mk (AdicTruncation.ideal S n) a)) = _
  exact AdicTruncation.residueEquiv_residue_mk S n a

/-- The compatible family of composites of `f : R ⟶ S` with the quotient maps
`S → S / m_S ^ (n + 1)`. -/
noncomputable def representableSectionMap
    (R S : CompleteLocalAlgCat.{u, v, w} Λ k) (f : R ⟶ S) :
    AdicSection (restrictedCoyoneda (Λ := Λ) (k := k) R) S where
  value n := f ≫ quotientProjection (Λ := Λ) (k := k) S n
  compatible n := by
    change f ≫ (quotientProjection (Λ := Λ) (k := k) S (n + 1) ≫
      artinianToComplete.map (AdicTruncation.transition S n)) =
      f ≫ quotientProjection (Λ := Λ) (k := k) S n
    apply congrArg (fun q => f ≫ q)
    apply CompleteLocalAlgCat.Hom.ext
    apply AlgHom.ext
    intro a
    rfl

/-- The zero algebra homomorphism into a quotient `S ⧸ I` that is the zero ring. -/
def zeroQuotientAlgHom (R S : Type*) [CommRing R] [CommRing S]
    [Algebra Λ R] [Algebra Λ S] (I : Ideal S) [Subsingleton (S ⧸ I)] :
    R →ₐ[Λ] S ⧸ I where
  toFun _ := 0
  map_zero' := Subsingleton.elim _ _
  map_one' := Subsingleton.elim _ _
  map_add' _ _ := Subsingleton.elim _ _
  map_mul' _ _ := Subsingleton.elim _ _
  commutes' _ := Subsingleton.elim _ _

/-- The algebra homomorphisms `R → S / m_S ^ n` underlying a compatible family of maps
`R ⟶ S / m_S ^ (n + 1)`; for `n = 0` the target is the zero ring. -/
noncomputable def representableSectionQuotientHom
    (R S : CompleteLocalAlgCat.{u, v, w} Λ k)
    (x : AdicSection (restrictedCoyoneda (Λ := Λ) (k := k) R) S) :
    (n : ℕ) → R →ₐ[Λ] S ⧸ (maximalIdeal S) ^ n
  | 0 => by
      letI : Subsingleton (S ⧸ (maximalIdeal S) ^ 0) := by
        apply Ideal.Quotient.subsingleton_iff.mpr
        simp
      exact zeroQuotientAlgHom (Λ := Λ) R S ((maximalIdeal S) ^ 0)
  | n + 1 => by
      refine { toRingHom := (x.value n).hom.toRingHom, commutes' := ?_ }
      intro a
      simp [AdicTruncation.obj, AdicTruncation.ideal, artinianToComplete]

/-- Any two algebra homomorphisms into `S ⧸ m_S ^ 0`, the zero ring, are equal. -/
private theorem algHom_quotient_pow_zero_ext
    {R S : CompleteLocalAlgCat.{u, v, w} Λ k} (f g : R →ₐ[Λ] S ⧸ (maximalIdeal S) ^ 0) :
    f = g :=
  haveI : Subsingleton (S ⧸ (maximalIdeal S) ^ 0) :=
    Ideal.Quotient.subsingleton_iff.mpr (by simp)
  Subsingleton.elim _ _

/-- The homomorphisms `representableSectionQuotientHom` are compatible with the quotient maps
`S / m_S ^ (n + 1) → S / m_S ^ n`. -/
theorem representableSectionQuotientHom_step
    (R S : CompleteLocalAlgCat.{u, v, w} Λ k)
    (x : AdicSection (restrictedCoyoneda (Λ := Λ) (k := k) R) S) (n : ℕ) :
    (Ideal.Quotient.factorₐ Λ (Ideal.pow_le_pow_right (Nat.le_succ n))).comp
      (representableSectionQuotientHom (Λ := Λ) (k := k) R S x (n + 1)) =
      representableSectionQuotientHom (Λ := Λ) (k := k) R S x n := by
  cases n with
  | zero => exact algHom_quotient_pow_zero_ext _ _
  | succ n =>
      apply AlgHom.ext
      intro a
      have hx := x.compatible n
      change (x.value (n + 1) ≫
        artinianToComplete.map (AdicTruncation.transition S n)) =
        x.value n at hx
      exact congrArg (fun q : R ⟶ _ => q.hom a) hx

/-- The homomorphisms `representableSectionQuotientHom` are compatible along every `m ≤ n`. -/
private theorem representableSectionQuotientHom_comp
    (R S : CompleteLocalAlgCat.{u, v, w} Λ k)
    (x : AdicSection (restrictedCoyoneda (Λ := Λ) (k := k) R) S) {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factorₐ Λ (Ideal.pow_le_pow_right hmn)).comp
      (representableSectionQuotientHom (Λ := Λ) (k := k) R S x n) =
      representableSectionQuotientHom (Λ := Λ) (k := k) R S x m := by
  cases m with
  | zero => exact algHom_quotient_pow_zero_ext _ _
  | succ m =>
      cases n with
      | zero => omega
      | succ n =>
          have hh := IsAdicComplete.StrictMono.factorPow_comp_eq_of_factorPow_comp_succ_eq'
            (I := maximalIdeal S) (strictMono_nat_of_lt_succ fun j => by omega)
            (fun j => (representableSectionQuotientHom (Λ := Λ) (k := k) R S x (j + 1)).toRingHom)
            (fun {j} => congrArg AlgHom.toRingHom
              (representableSectionQuotientHom_step (Λ := Λ) (k := k) R S x (j + 1)))
            (Nat.succ_le_succ_iff.mp hmn)
          exact AlgHom.ext fun a =>
            congrArg (fun q : R →+* S ⧸ (maximalIdeal S) ^ (m + 1) => q a) hh

/-- The algebra homomorphism `R → S` that is the limit of a compatible family of maps
`R → S / m_S ^ (n + 1)`, using that `S` is complete. -/
noncomputable def representableSectionLiftAlgHom
    (R S : CompleteLocalAlgCat.{u, v, w} Λ k)
    (x : AdicSection (restrictedCoyoneda (Λ := Λ) (k := k) R) S) :
    R →ₐ[Λ] S := by
  let f := representableSectionQuotientHom (Λ := Λ) (k := k) R S x
  have hf : ∀ {m n : ℕ} (hmn : m ≤ n),
      (Ideal.Quotient.factorₐ Λ (Ideal.pow_le_pow_right hmn)).comp (f n) = f m := by
    intro m n hmn
    cases m with
    | zero =>
        have : Subsingleton (S ⧸ (maximalIdeal S) ^ 0) :=
          Ideal.Quotient.subsingleton_iff.mpr (by simp)
        exact Subsingleton.elim _ _
    | succ m =>
        cases n with
        | zero => omega
        | succ n =>
            have hh := IsAdicComplete.StrictMono.factorPow_comp_eq_of_factorPow_comp_succ_eq'
              (I := maximalIdeal S) (strictMono_nat_of_lt_succ fun j => by omega)
              (fun j => (f (j + 1)).toRingHom)
              (fun {j} => congrArg AlgHom.toRingHom
                (representableSectionQuotientHom_step (Λ := Λ) (k := k) R S x (j + 1)))
              (Nat.succ_le_succ_iff.mp hmn)
            exact AlgHom.ext fun a =>
              congrArg (fun q : R →+* S ⧸ (maximalIdeal S) ^ (m + 1) => q a) hh
  letI : IsAdicComplete (maximalIdeal S) S := S.completeLocal.isComplete
  exact ((AdicCompletion.ofAlgEquiv (maximalIdeal S)).symm.restrictScalars Λ).toAlgHom.comp
    (AdicCompletion.liftAlgHom (maximalIdeal S) f hf)

/-- The homomorphism `representableSectionLiftAlgHom` reduces modulo `m_S ^ (n + 1)` to the
`n`-th member of the family. -/
theorem representableSectionLift_quotient
    (R S : CompleteLocalAlgCat.{u, v, w} Λ k)
    (x : AdicSection (restrictedCoyoneda (Λ := Λ) (k := k) R) S)
    (n : ℕ) (a : R) :
    (quotientProjection (Λ := Λ) (k := k) S n).hom
        (representableSectionLiftAlgHom (Λ := Λ) (k := k) R S x a) =
      (x.value n).hom a := by
  let f := representableSectionQuotientHom (Λ := Λ) (k := k) R S x
  have hf := fun {m n : ℕ} (hmn : m ≤ n) =>
    representableSectionQuotientHom_comp (Λ := Λ) (k := k) R S x hmn
  let : IsAdicComplete (maximalIdeal S) S := S.completeLocal.isComplete
  show Ideal.Quotient.mk (maximalIdeal S ^ (n + 1))
    ((AdicCompletion.ofAlgEquiv (maximalIdeal S)).symm
      ((AdicCompletion.liftAlgHom (maximalIdeal S) f hf) a)) = f (n + 1) a
  rw [AdicCompletion.mk_ofAlgEquiv_symm, AdicCompletion.evalₐ_liftAlgHom]

/-- The morphism of complete local algebras `R ⟶ S` determined by a compatible family of maps
from `R` to the Artinian quotients of `S`. -/
noncomputable def representableSectionLift
    (R S : CompleteLocalAlgCat.{u, v, w} Λ k)
    (x : AdicSection (restrictedCoyoneda (Λ := Λ) (k := k) R) S) : R ⟶ S := by
  let F := representableSectionLiftAlgHom (Λ := Λ) (k := k) R S x
  refine ⟨F, ?_, ?_⟩
  · refine ⟨fun a ha => ?_⟩
    have hunit' := (quotientProjection (Λ := Λ) (k := k) S 0).hom.isUnit_map ha
    change IsUnit ((quotientProjection (Λ := Λ) (k := k) S 0).hom (F a)) at hunit'
    rw [representableSectionLift_quotient (Λ := Λ) (k := k) R S x 0 a] at hunit'
    exact (x.value 0).isLocal.map_nonunit a hunit'
  · intro a
    rw [← AdicTruncation.residueEquiv_residue_mk S 0 (F a)]
    let : Nontrivial (S ⧸ AdicTruncation.ideal S 0) := by
      apply Ideal.Quotient.nontrivial_iff.mpr
      exact ((Ideal.pow_le_self (by omega)).trans_lt (maximalIdeal.isMaximal S).lt_top).ne
    let : IsLocalRing (S ⧸ AdicTruncation.ideal S 0) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
    change AdicTruncation.residueEquiv S 0
      (residue (S ⧸ AdicTruncation.ideal S 0)
        ((quotientProjection (Λ := Λ) (k := k) S 0).hom (F a))) = _
    rw [representableSectionLift_quotient (Λ := Λ) (k := k) R S x 0 a]
    exact (x.value 0).residue_comm a

/-- The quotient maps `S → S / m_S ^ (n + 1)` are natural in morphisms of complete local
algebras. -/
theorem quotientProjection_naturality
    (S T : CompleteLocalAlgCat.{u, v, w} Λ k) (f : S ⟶ T) (n : ℕ) :
    quotientProjection (Λ := Λ) (k := k) S n ≫
      artinianToComplete.map (AdicTruncation.map f n) =
    f ≫ quotientProjection (Λ := Λ) (k := k) T n := by
  apply CompleteLocalAlgCat.Hom.ext
  apply AlgHom.ext
  intro a
  rfl

/-- Morphisms `R ⟶ S` of complete local algebras correspond bijectively to compatible families
of maps from `R` to the Artinian quotients of `S`. -/
noncomputable def representableSectionEquiv
    (R S : CompleteLocalAlgCat.{u, v, w} Λ k) :
    (R ⟶ S) ≃ AdicSection (restrictedCoyoneda (Λ := Λ) (k := k) R) S where
  toFun := representableSectionMap (Λ := Λ) (k := k) R S
  invFun := representableSectionLift (Λ := Λ) (k := k) R S
  left_inv f := by
    apply CompleteLocalAlgCat.Hom.ext
    apply DFunLike.coe_injective
    apply IsHausdorff.StrictMono.funext' (maximalIdeal S)
      (a := fun n : ℕ => n + 1)
      (strictMono_nat_of_lt_succ fun n => Nat.lt_succ_self (n + 1))
    intro n a
    change (quotientProjection (Λ := Λ) (k := k) S n).hom
        (representableSectionLiftAlgHom (Λ := Λ) (k := k) R S
          (representableSectionMap (Λ := Λ) (k := k) R S f) a) =
      (quotientProjection (Λ := Λ) (k := k) S n).hom (f.hom a)
    rw [representableSectionLift_quotient]
    rfl
  right_inv x := by
    apply AdicSection.ext
    intro n
    apply CompleteLocalAlgCat.Hom.ext
    apply AlgHom.ext
    intro a
    change (quotientProjection (Λ := Λ) (k := k) S n).hom
      (representableSectionLiftAlgHom (Λ := Λ) (k := k) R S x a) = (x.value n).hom a
    rw [representableSectionLift_quotient]

/-- The covariant functor represented by `R` is canonically the adic completion
of its restriction to Artinian local algebras. -/
@[stacks 06HE "representable_completion", sga "3 XI 3.3" "representable, affine"]
public noncomputable def coyonedaIsoAdicCompletion
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) :
    coyoneda.obj (Opposite.op R) ≅
      adicCompletion (artinianToComplete ⋙
        coyoneda.obj (Opposite.op R)) := by
  refine NatIso.ofComponents
    (fun S => (representableSectionEquiv (Λ := Λ) (k := k) R S).toIso) ?_
  intro S T f
  ext g
  apply AdicSection.ext
  intro n
  apply CompleteLocalAlgCat.Hom.ext
  apply AlgHom.ext
  intro a
  rfl

/-- At level `n`, the canonical isomorphism sends `f : R ⟶ S` to the composite
of `f` with the quotient homomorphism `S → S / m_S ^ (n + 1)`. -/
@[stacks 06HE "representable_completion"]
public theorem coyonedaIsoAdicCompletion_hom_apply
    (R S : CompleteLocalAlgCat.{u, v, w} Λ k) (f : R ⟶ S) (n : ℕ) :
    (((coyonedaIsoAdicCompletion R).hom.app S f).value n).hom =
      (Ideal.Quotient.mkₐ Λ (AdicTruncation.ideal S n)).comp f.hom :=
  rfl

end

/-! ### Completion of a limit-preserving functor -/

section
open CategoryTheory CategoryTheory.Limits
open IsLocalRing
universe u v w


variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- For `m ≤ n`, the quotient map `R / m_R ^ (n + 1) → R / m_R ^ (m + 1)`. -/
noncomputable def truncationMapLE
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) {m n : ℕ} (h : m ≤ n) :
    AdicTruncation.obj R n ⟶ AdicTruncation.obj R m := by
  let I := AdicTruncation.ideal R n
  let J := AdicTruncation.ideal R m
  letI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr
    ((Ideal.pow_le_self (Nat.succ_ne_zero n)).trans_lt (maximalIdeal.isMaximal R).lt_top).ne
  letI : IsLocalRing (R ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  letI : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr
    ((Ideal.pow_le_self (Nat.succ_ne_zero m)).trans_lt (maximalIdeal.isMaximal R).lt_top).ne
  letI : IsLocalRing (R ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  have hIJ : I ≤ J := Ideal.pow_le_pow_right (Nat.add_le_add_right h 1)
  let f := Ideal.Quotient.factorₐ Λ hIJ
  refine
    { hom := f
      isLocal := IsLocalHom.of_surjective _ (Ideal.Quotient.factor_surjective hIJ)
      residue_comm := ?_ }
  intro x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  change AdicTruncation.residueEquiv R m
      (residue (R ⧸ J) (Ideal.Quotient.mk J r)) =
    AdicTruncation.residueEquiv R n
      (residue (R ⧸ I) (Ideal.Quotient.mk I r))
  rw [AdicTruncation.residueEquiv_residue_mk,
    AdicTruncation.residueEquiv_residue_mk]


/-- The quotient map `truncationMapLE` for `n ≤ n` is the identity. -/
theorem truncationMapLE_refl
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (n : ℕ) :
    truncationMapLE R (le_rfl : n ≤ n) = 𝟙 (AdicTruncation.obj R n) := by
  apply ArtinianLocalAlgCat.hom_ext
  apply AlgHom.ext
  intro x
  simp [truncationMapLE, Ideal.Quotient.factorₐ_refl]
  rfl

/-- The quotient maps `truncationMapLE` compose to the quotient map `truncationMapLE`. -/
theorem truncationMapLE_comp
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) {l m n : ℕ}
    (hlm : l ≤ m) (hmn : m ≤ n) :
    truncationMapLE R hmn ≫ truncationMapLE R hlm =
      truncationMapLE R (hlm.trans hmn) := by
  apply ArtinianLocalAlgCat.hom_ext
  apply AlgHom.ext
  intro x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  let I := AdicTruncation.ideal R n
  let J := AdicTruncation.ideal R m
  let K := AdicTruncation.ideal R l
  have hIJ : I ≤ J := Ideal.pow_le_pow_right (Nat.add_le_add_right hmn 1)
  have hJK : J ≤ K := Ideal.pow_le_pow_right (Nat.add_le_add_right hlm 1)
  have hIK : I ≤ K := hIJ.trans hJK
  show (Ideal.Quotient.factorₐ Λ hJK) ((Ideal.Quotient.factorₐ Λ hIJ) (Ideal.Quotient.mk I r)) =
    Ideal.Quotient.factorₐ Λ hIK (Ideal.Quotient.mk I r)
  simp

/-- The inverse system of the quotients `S / m_S ^ (n + 1)`, as complete local algebras
indexed by `ℕᵒᵖ`. -/
noncomputable def adicQuotientDiagram
    (S : CompleteLocalAlgCat.{u, v, w} Λ k) :
    ℕᵒᵖ ⥤ CompleteLocalAlgCat.{u, v, w} Λ k where
  obj i := artinianToComplete.obj (AdicTruncation.obj S i.unop)
  map f := artinianToComplete.map
    (truncationMapLE S f.unop.le)
  map_id i := by
    change artinianToComplete.map
        (truncationMapLE S (le_rfl : i.unop ≤ i.unop)) = 𝟙 _
    rw [truncationMapLE_refl]
    exact artinianToComplete.map_id _
  map_comp f g := by
    change artinianToComplete.map
        (truncationMapLE S ((f ≫ g).unop.le)) =
      artinianToComplete.map (truncationMapLE S f.unop.le) ≫
        artinianToComplete.map (truncationMapLE S g.unop.le)
    rw [← Functor.map_comp, truncationMapLE_comp]

/-- The cone over `adicQuotientDiagram S` with apex `S`, given by the quotient maps. -/
noncomputable def adicQuotientCone
    (S : CompleteLocalAlgCat.{u, v, w} Λ k) : Cone (adicQuotientDiagram S) where
  pt := S
  π := {
    app := fun i => {
      hom := Ideal.Quotient.mkₐ Λ (AdicTruncation.ideal S i.unop)
      isLocal := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
      residue_comm := by
        intro x
        exact AdicTruncation.residueEquiv_residue_mk S i.unop x }
    naturality := by
      intro i j f
      apply CompleteLocalAlgCat.Hom.ext
      apply AlgHom.ext
      intro x
      rfl }

/-- The morphism `n + 1 ⟶ n` in `ℕᵒᵖ`. -/
def adicAdjacentArrow (n : ℕ) :
    Opposite.op (n + 1) ⟶ (Opposite.op n : ℕᵒᵖ) :=
  Quiver.Hom.op (homOfLE (Nat.le_succ n))

/-- The quotient map `truncationMapLE` for `n ≤ n + 1` is `AdicTruncation.transition`. -/
theorem truncationMapLE_succ
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (n : ℕ) :
    truncationMapLE R (Nat.le_succ n) = AdicTruncation.transition R n := by
  apply ArtinianLocalAlgCat.hom_ext
  apply AlgHom.ext
  intro x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp [truncationMapLE, AdicTruncation.transition]

/-- The values of a compatible family at levels `m ≤ n` correspond under the quotient map
`truncationMapLE`. -/
theorem adicSection_compatible_le
    {F : ArtinianLocalAlgCat.{u, v, w} Λ k ⥤ Type v}
    {S : CompleteLocalAlgCat.{u, v, w} Λ k}
    (s : AdicSection F S) {m n : ℕ} (h : m ≤ n) :
    F.map (truncationMapLE S h) (s.value n) = s.value m := by
  induction n, h using Nat.le_induction with
  | base =>
      rw [truncationMapLE_refl, F.map_id]
      rfl
  | @succ n h ih =>
      rw [← truncationMapLE_comp S h (Nat.le_succ n), F.map_comp,
        truncationMapLE_succ]
      show F.map (truncationMapLE S h)
        (F.map (AdicTruncation.transition S n) (s.value (n + 1))) = s.value m
      rw [s.compatible n, ih]

/-- The map `n ↦ n + 1` on `ℕ` is strictly monotone. -/
theorem adicSuccStrictMono : StrictMono (fun n : ℕ => n + 1) :=
  fun _ _ h => Nat.add_lt_add_right h 1

/-- The transition map `S / m_S ^ (n + 2) → S / m_S ^ (n + 1)` is
`Ideal.Quotient.factorPow`. -/
theorem quotientTransition_factorPow
    (S : CompleteLocalAlgCat.{u, v, w} Λ k) (n : ℕ) :
    (Ideal.Quotient.factorPow (maximalIdeal S) (Nat.le_succ (n + 1))) =
      (AdicTruncation.transition S n).hom.toRingHom := by
  show (Ideal.Quotient.factorPow (maximalIdeal S) (Nat.le_succ (n + 1)) :
      S ⧸ maximalIdeal S ^ (n + 2) →+* S ⧸ maximalIdeal S ^ (n + 1)) =
    (Ideal.Quotient.factor (show maximalIdeal S ^ (n + 2) ≤
      maximalIdeal S ^ (n + 1) from Ideal.pow_le_pow_right (Nat.le_succ (n + 1))) :
      S ⧸ maximalIdeal S ^ (n + 2) →+* S ⧸ maximalIdeal S ^ (n + 1))
  rfl

/-- The ring homomorphisms from the apex of a cone over `adicQuotientDiagram S` to the quotients
`S / m_S ^ (n + 1)`. -/
def adicQuotientConeFamily
    (S : CompleteLocalAlgCat.{u, v, w} Λ k)
    (t : Cone (adicQuotientDiagram S)) (n : ℕ) :
    t.pt →+* S ⧸ maximalIdeal S ^ (n + 1) :=
  (t.π.app (Opposite.op n)).hom.toRingHom

/-- The family `adicQuotientConeFamily` is compatible with the quotient maps
`S / m_S ^ (n + 2) → S / m_S ^ (n + 1)`. -/
theorem adicQuotientConeFamily_compatible
    (S : CompleteLocalAlgCat.{u, v, w} Λ k)
    (t : Cone (adicQuotientDiagram S)) : ∀ {n : ℕ},
      (Ideal.Quotient.factorPow (maximalIdeal S) (Nat.le_succ (n + 1))).comp
          (adicQuotientConeFamily S t (n + 1)) = adicQuotientConeFamily S t n := by
  intro n
  have hw := congrArg CompleteLocalAlgCat.Hom.hom
    (t.w (adicAdjacentArrow n))
  change (artinianToComplete.map
      (truncationMapLE S (Nat.le_succ n))).hom.comp
      (t.π.app (Opposite.op (n + 1))).hom =
    (t.π.app (Opposite.op n)).hom at hw
  rw [truncationMapLE_succ] at hw
  have hwRing := congrArg AlgHom.toRingHom hw
  change (AdicTruncation.transition S n).hom.toRingHom.comp
      (adicQuotientConeFamily S t (n + 1)) = adicQuotientConeFamily S t n at hwRing
  rw [← quotientTransition_factorPow S n] at hwRing
  exact hwRing

/-- The ring homomorphism from the apex of a cone over `adicQuotientDiagram S` to `S`, obtained
from the completeness of `S`. -/
noncomputable def adicQuotientConeLiftRingHom
    (S : CompleteLocalAlgCat.{u, v, w} Λ k)
    (t : Cone (adicQuotientDiagram S)) : t.pt →+* S :=
  IsAdicComplete.StrictMono.liftRingHom (maximalIdeal S) adicSuccStrictMono
    (adicQuotientConeFamily S t) (adicQuotientConeFamily_compatible S t)

/-- The ring homomorphism `adicQuotientConeLiftRingHom` reduces modulo `m_S ^ (n + 1)` to the
`n`-th leg of the cone. -/
theorem adicQuotientConeLiftRingHom_mk
    (S : CompleteLocalAlgCat.{u, v, w} Λ k)
    (t : Cone (adicQuotientDiagram S)) (n : ℕ) (x : t.pt) :
    Ideal.Quotient.mk (maximalIdeal S ^ (n + 1)) (adicQuotientConeLiftRingHom S t x) =
      adicQuotientConeFamily S t n x :=
  IsAdicComplete.StrictMono.mk_liftRingHom
    (I := maximalIdeal S) (ha := adicSuccStrictMono)
    (f := adicQuotientConeFamily S t)
    (hf := adicQuotientConeFamily_compatible S t) (n := n) x

/-- The morphism of complete local algebras from the apex of a cone over `adicQuotientDiagram S`
to `S`. -/
noncomputable def adicQuotientConeLift
    (S : CompleteLocalAlgCat.{u, v, w} Λ k)
    (t : Cone (adicQuotientDiagram S)) : t.pt ⟶ S := by
  let lift : t.pt →+* S := adicQuotientConeLiftRingHom S t
  let alg : t.pt →ₐ[Λ] S := {
    __ := lift
    commutes' := by
      intro r
      have heq :
          (fun r : Λ => lift (algebraMap Λ t.pt r)) = fun r => algebraMap Λ S r := by
        apply IsHausdorff.StrictMono.funext' (maximalIdeal S) adicSuccStrictMono
        intro n a
        change Ideal.Quotient.mk (maximalIdeal S ^ (n + 1))
            (lift (algebraMap Λ t.pt a)) = algebraMap Λ (S ⧸ maximalIdeal S ^ (n + 1)) a
        have hmk := IsAdicComplete.StrictMono.mk_liftRingHom
          (I := maximalIdeal S) (ha := adicSuccStrictMono)
          (f := adicQuotientConeFamily S t)
          (hf := adicQuotientConeFamily_compatible S t)
          (n := n) (algebraMap Λ t.pt a)
        rw [show Ideal.Quotient.mk (maximalIdeal S ^ (n + 1))
            (lift (algebraMap Λ t.pt a)) =
              adicQuotientConeFamily S t n (algebraMap Λ t.pt a) by
              simpa [lift, adicQuotientConeLiftRingHom] using hmk]
        change (t.π.app (Opposite.op n)).hom (algebraMap Λ t.pt a) =
          algebraMap Λ (AdicTruncation.obj S n) a
        exact (t.π.app (Opposite.op n)).hom.commutes a
      exact congrFun heq r }
  have hquot (x : t.pt) :
      Ideal.Quotient.mk (AdicTruncation.ideal S 0) (alg x) =
        adicQuotientConeFamily S t 0 x := by
    simpa [alg, lift, adicQuotientConeLiftRingHom, AdicTruncation.ideal, pow_one] using
      adicQuotientConeLiftRingHom_mk S t 0 x
  refine {
    hom := alg
    isLocal := ⟨by
      intro x hunit
      have hunitQ : IsUnit
          (Ideal.Quotient.mk (AdicTruncation.ideal S 0) (alg x)) :=
        hunit.map (Ideal.Quotient.mk (AdicTruncation.ideal S 0))
      rw [hquot x] at hunitQ
      exact (t.π.app (Opposite.op 0)).isLocal.map_nonunit x hunitQ⟩
    residue_comm := by
      intro x
      calc
        S.residueEquiv (residue S (alg x)) =
            (AdicTruncation.obj S 0).residueEquiv
              (residue (AdicTruncation.obj S 0)
                (Ideal.Quotient.mk (AdicTruncation.ideal S 0) (alg x))) := by
                  symm
                  exact AdicTruncation.residueEquiv_residue_mk S 0 (alg x)
        _ = (AdicTruncation.obj S 0).residueEquiv
              (residue (AdicTruncation.obj S 0)
                ((t.π.app (Opposite.op 0)).hom x)) :=
                  congrArg (fun y => (AdicTruncation.obj S 0).residueEquiv
                    (residue (AdicTruncation.obj S 0) y)) (hquot x)
        _ = t.pt.residueEquiv (residue t.pt x) :=
              (t.π.app (Opposite.op 0)).residue_comm x }

/-- The morphism `adicQuotientConeLift` composed with each quotient map is the corresponding leg
of the cone. -/
theorem adicQuotientConeLift_fac
    (S : CompleteLocalAlgCat.{u, v, w} Λ k)
    (t : Cone (adicQuotientDiagram S)) (n : ℕ) :
    adicQuotientConeLift S t ≫ (adicQuotientCone S).π.app (Opposite.op n) =
      t.π.app (Opposite.op n) := by
  apply CompleteLocalAlgCat.Hom.ext
  apply AlgHom.ext
  intro x
  show Ideal.Quotient.mk (AdicTruncation.ideal S n)
      ((adicQuotientConeLift S t).hom x) = adicQuotientConeFamily S t n x
  simpa [adicQuotientConeLift, AdicTruncation.ideal] using
    adicQuotientConeLiftRingHom_mk S t n x

/-- A complete local algebra is the limit of its quotients `S / m_S ^ (n + 1)`. -/
noncomputable def adicQuotientConeIsLimit
    (S : CompleteLocalAlgCat.{u, v, w} Λ k) : IsLimit (adicQuotientCone S) where
  lift := adicQuotientConeLift S
  fac t j := adicQuotientConeLift_fac S t j.unop
  uniq := by
    intro t f hf
    apply CompleteLocalAlgCat.Hom.ext
    apply AlgHom.ext
    intro x
    have heq : (fun _ : Unit => f.hom x) =
        fun _ : Unit => (adicQuotientConeLift S t).hom x := by
      apply IsHausdorff.StrictMono.funext' (maximalIdeal S) adicSuccStrictMono
      intro n _
      have hf' := congrArg CompleteLocalAlgCat.Hom.hom (hf (Opposite.op n))
      have hl' := congrArg CompleteLocalAlgCat.Hom.hom
        (adicQuotientConeLift_fac S t n)
      have hfx := congrArg (fun g : t.pt →ₐ[Λ] AdicTruncation.obj S n => g x) hf'
      have hlx := congrArg (fun g : t.pt →ₐ[Λ] AdicTruncation.obj S n => g x) hl'
      change Ideal.Quotient.mk (AdicTruncation.ideal S n) (f.hom x) =
        (t.π.app (Opposite.op n)).hom x at hfx
      change Ideal.Quotient.mk (AdicTruncation.ideal S n)
          ((adicQuotientConeLift S t).hom x) =
        (t.π.app (Opposite.op n)).hom x at hlx
      exact hfx.trans hlx.symm
    exact congrFun heq ()

/-- The compatible family of images of `x : G.obj S` on the quotients `S / m_S ^ (n + 1)`. -/
noncomputable def adicCompletionRestrictionForward
    (G : CompleteLocalAlgCat.{u, v, w} Λ k ⥤ Type v)
    (S : CompleteLocalAlgCat.{u, v, w} Λ k) [PreservesLimits G]
    (x : G.obj S) : AdicSection (artinianToComplete ⋙ G) S where
  value n := G.map ((adicQuotientCone S).π.app (Opposite.op n)) x
  compatible n := by
    change (G.map ((adicQuotientCone S).π.app (Opposite.op (n + 1))) ≫
        G.map (artinianToComplete.map (AdicTruncation.transition S n))) x =
      G.map ((adicQuotientCone S).π.app (Opposite.op n)) x
    let q := (adicQuotientCone S).π.app (Opposite.op (n + 1))
    let r := artinianToComplete.map (AdicTruncation.transition S n)
    have hw := (adicQuotientCone S).w (adicAdjacentArrow n)
    change (adicQuotientCone S).π.app (Opposite.op (n + 1)) ≫
        artinianToComplete.map (AdicTruncation.transition S n) =
      (adicQuotientCone S).π.app (Opposite.op n) at hw
    exact (congrArg (fun f => f x) (G.map_comp q r)).symm.trans
      (congrArg (fun f => G.map f x) hw)

/-- The cone over `adicQuotientDiagram S ⋙ G` with a one-point apex, given by a compatible
family. -/
noncomputable def adicSectionCone
    (G : CompleteLocalAlgCat.{u, v, w} Λ k ⥤ Type v)
    (S : CompleteLocalAlgCat.{u, v, w} Λ k)
    (s : AdicSection (artinianToComplete ⋙ G) S) :
    Cone (adicQuotientDiagram S ⋙ G) where
  pt := PUnit.{v + 1}
  π := {
    app := fun i => TypeCat.ofHom (fun (_ : PUnit.{v + 1}) => s.value i.unop)
    naturality := by
      intro i j f
      ext
      change s.value j.unop = G.map (artinianToComplete.map
        (truncationMapLE S f.unop.le)) (s.value i.unop)
      exact (adicSection_compatible_le s f.unop.le).symm }

/-- For a limit-preserving functor `G`, the value on `S` glued from a compatible family of values
on the quotients `S / m_S ^ (n + 1)`. -/
noncomputable def adicCompletionRestrictionBackward
    (G : CompleteLocalAlgCat.{u, v, w} Λ k ⥤ Type v)
    (S : CompleteLocalAlgCat.{u, v, w} Λ k) [PreservesLimits G]
    (s : AdicSection (artinianToComplete ⋙ G) S) : G.obj S :=
  letI := preservesSmallestLimits_of_preservesLimits G
  (isLimitOfPreserves G (adicQuotientConeIsLimit S)).lift
    (adicSectionCone G S s) PUnit.unit

/-- Gluing a compatible family and then restricting to the quotients returns the family. -/
theorem adicCompletionRestrictionForward_backward
    (G : CompleteLocalAlgCat.{u, v, w} Λ k ⥤ Type v)
    (S : CompleteLocalAlgCat.{u, v, w} Λ k) [PreservesLimits G]
    (s : AdicSection (artinianToComplete ⋙ G) S) :
    adicCompletionRestrictionForward G S (adicCompletionRestrictionBackward G S s) = s := by
  let := preservesSmallestLimits_of_preservesLimits G
  exact AdicSection.ext fun n => congrArg (fun f => f PUnit.unit)
    ((isLimitOfPreserves G (adicQuotientConeIsLimit S)).fac (adicSectionCone G S s) (.op n))

/-- Restricting a value to the quotients and then gluing returns the value. -/
theorem adicCompletionRestrictionBackward_forward
    (G : CompleteLocalAlgCat.{u, v, w} Λ k ⥤ Type v)
    (S : CompleteLocalAlgCat.{u, v, w} Λ k) [PreservesLimits G]
    (x : G.obj S) :
    adicCompletionRestrictionBackward G S (adicCompletionRestrictionForward G S x) = x := by
  let := preservesSmallestLimits_of_preservesLimits G
  let c := adicSectionCone G S (adicCompletionRestrictionForward G S x)
  let m : PUnit.{v + 1} ⟶ G.obj S := TypeCat.ofHom (fun _ => x)
  have hm : ∀ j, m ≫ (G.mapCone (adicQuotientCone S)).π.app j = c.π.app j := fun _ => rfl
  have h := (isLimitOfPreserves G (adicQuotientConeIsLimit S)).uniq c m hm
  exact (congrArg (fun f => f PUnit.unit) h).symm

/-- For a limit-preserving functor `G`, values of `G` on `S` correspond bijectively to compatible
families of values on the quotients `S / m_S ^ (n + 1)`. -/
noncomputable def adicCompletionRestrictionEquiv
    (G : CompleteLocalAlgCat.{u, v, w} Λ k ⥤ Type v) [PreservesLimits G]
    (S : CompleteLocalAlgCat.{u, v, w} Λ k) :
    G.obj S ≃ AdicSection (artinianToComplete ⋙ G) S where
  toFun := adicCompletionRestrictionForward G S
  invFun := adicCompletionRestrictionBackward G S
  left_inv := adicCompletionRestrictionBackward_forward G S
  right_inv := adicCompletionRestrictionForward_backward G S

/-- The bijection `adicCompletionRestrictionEquiv` as an isomorphism of types. -/
noncomputable def adicCompletionRestrictionComponent
    (G : CompleteLocalAlgCat.{u, v, w} Λ k ⥤ Type v) [PreservesLimits G]
    (S : CompleteLocalAlgCat.{u, v, w} Λ k) :
    G.obj S ≅ AdicSection (artinianToComplete ⋙ G) S :=
  (adicCompletionRestrictionEquiv G S).toIso

/-- The legs of `adicQuotientCone` are natural in morphisms of complete local algebras. -/
theorem adicQuotientCone_naturality
    {S T : CompleteLocalAlgCat.{u, v, w} Λ k} (f : S ⟶ T) (n : ℕ) :
    (adicQuotientCone S).π.app (Opposite.op n) ≫
        artinianToComplete.map (AdicTruncation.map f n) =
      f ≫ (adicQuotientCone T).π.app (Opposite.op n) :=
  quotientProjection_naturality _ _ f n

/-- A limit-preserving functor on complete local algebras is canonically the
completion of its restriction to Artinian local algebras. -/
@[stacks 06HE "continuous_functor_completion"]
public noncomputable def adicCompletionRestrictionIso
    (G : CompleteLocalAlgCat.{u, v, w} Λ k ⥤ Type v)
    [PreservesLimits G] :
    G ≅ adicCompletion (artinianToComplete ⋙ G) := by
  refine NatIso.ofComponents (fun S => adicCompletionRestrictionComponent G S) ?_
  intro S T f
  ext x
  apply AdicSection.ext
  intro n
  change G.map ((adicQuotientCone T).π.app (Opposite.op n)) (G.map f x) =
    G.map (artinianToComplete.map (AdicTruncation.map f n))
      (G.map ((adicQuotientCone S).π.app (Opposite.op n)) x)
  let qS := (adicQuotientCone S).π.app (Opposite.op n)
  let qT := (adicQuotientCone T).π.app (Opposite.op n)
  let r := artinianToComplete.map (AdicTruncation.map f n)
  have h1 : G.map qT (G.map f x) = G.map (f ≫ qT) x :=
    (congrArg (fun h => h x) (G.map_comp f qT)).symm
  have hnat := congrArg (fun g : S ⟶ artinianToComplete.obj
      (AdicTruncation.obj T n) => G.map g)
      (adicQuotientCone_naturality f n).symm
  have h2 : G.map (f ≫ qT) x = G.map (qS ≫ r) x :=
    congrArg (fun h => h x) hnat
  have h3 : G.map (qS ≫ r) x = G.map r (G.map qS x) :=
    congrArg (fun h => h x) (G.map_comp qS r)
  exact h1.trans (h2.trans h3)

/-- The canonical isomorphism sends a value to its image on each adic quotient.
The formula is independent of the chosen morphism representing that quotient. -/
@[stacks 06HE "continuous_functor_completion"]
public theorem adicCompletionRestrictionIso_hom_apply
    (G : CompleteLocalAlgCat.{u, v, w} Λ k ⥤ Type v)
    [PreservesLimits G]
    (S : CompleteLocalAlgCat.{u, v, w} Λ k) (x : G.obj S) (n : ℕ)
    (q : S ⟶ artinianToComplete.obj (AdicTruncation.obj S n))
    (hq : q.hom = Ideal.Quotient.mkₐ Λ (AdicTruncation.ideal S n)) :
    ((adicCompletionRestrictionIso G).hom.app S x).value n = G.map q x := by
  show G.map ((adicQuotientCone S).π.app (Opposite.op n)) x = G.map q x
  exact congrArg (fun q => G.map q x) (CompleteLocalAlgCat.Hom.ext hq.symm)

end

end Deformation
