module

public import Mathlib.Algebra.Algebra.Epi
public import Mathlib.Algebra.Category.Ring.Epi
public import Mathlib.Algebra.Category.Ring.Instances
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Under.Limits
public import Mathlib.Algebra.Field.ULift
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.Tensor
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.Pi
public import Mathlib.RingTheory.Valuation.LocalSubring
public import Mathlib.RingTheory.Valuation.ValuationRing
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.WeaklyEtale.Basic
public import StacksFrontier.RingTheory.WeaklyEtale.Flat

@[expose] public section

/-!
# Rings of weak dimension at most one

A commutative ring has weak dimension at most one exactly when every finitely generated ideal
of it is flat. This file records that intrinsic characterization and its three consequences for
integral closure: a product of valuation rings has weak dimension at most one and its ring of
componentwise fractions is a localization; a normal domain and its fraction field sit in a
cartesian square whose lower-left corner has weak dimension at most one; a flat injective ring
epimorphism out of a ring of weak dimension at most one adds no integral elements; and a weakly
étale algebra over a normal domain is integrally closed in its extension to the fraction field.

## Main definitions

* `HasWeakDimensionLEOne`: the intrinsic characterization of weak dimension at most one,
  flatness of every finitely generated ideal.

## Main results

* `weakDimensionLE_one_and_isLocalization_pi_fractionRing` (Stacks 092T): a product of valuation
  rings has weak dimension at most one, and the product of their fraction fields is its
  localization at the componentwise non-zero-divisors.
* `exists_isPullback_with_weakDimensionLE_one` (Stacks 092U): a normal domain and its fraction
  field fit into a cartesian square whose lower-left ring has weak dimension at most one and
  whose lower map is flat, injective and a ring epimorphism.
* `isIntegrallyClosedIn_of_isEpi_of_flat_of_weakDimensionLE_one` (Stacks 092V): a flat injective
  ring epimorphism whose source has weak dimension at most one makes the source integrally
  closed in the target.
* `isIntegrallyClosedIn_tensorProduct_fractionField_of_weaklyEtale` (Stacks 092W): a weakly
  étale algebra over a normal domain is integrally closed after base change to the fraction
  field.
* `flat_submodule_of_flat_of_weakDimensionLE_one`: over a ring of weak dimension at most one
  every submodule of a flat module is flat; this is the implication (3) ⟹ (4) of Stacks 092S,
  used again by `StacksFrontier.RingTheory.WeakDimension.DimensionOne`.

## Implementation notes

Weak dimension at most one is expressed throughout by `HasWeakDimensionLEOne`, condition (3) of
Stacks 092S, rather than by `HasWeakDimensionLE` of `StacksFrontier.RingTheory.WeaklyEtale.Defs`.
The equivalence of the two is Stacks 092S, proved in
`StacksFrontier.RingTheory.WeakDimension.DimensionOne`; it rests on the derived-category
characterization of Tor dimension by finite flat resolutions (Stacks 066F), so it is kept out of
this file, which needs none of that machinery.

For the same reason weak dimension at most one is propagated along a weakly étale map directly
rather than through Stacks 092E: if every finitely generated ideal of `A` is flat then every
submodule of a flat `A`-module is flat, so an ideal of a weakly étale `A`-algebra `B` is flat
over `A`, hence flat over `B` by Stacks 092C.

A valuation ring in Mathlib includes the domain condition, so for a localization at a prime the
corresponding domain and valuation-ring structures are asserted existentially. The cartesian
square of Stacks 092U is expressed in `CommRingCat`, lifting the two input rings to a common
universe; a normal domain is represented by `IsDomain` together with `IsIntegrallyClosed`, the
fraction field by any `IsFractionRing` model, and relative integral closure by
`IsIntegrallyClosedIn`. Ring epimorphisms are `Algebra.IsEpi`.

## References

* [The Stacks Project, Tag 092T](https://stacks.math.columbia.edu/tag/092T)
* [The Stacks Project, Tag 092U](https://stacks.math.columbia.edu/tag/092U)
* [The Stacks Project, Tag 092V](https://stacks.math.columbia.edu/tag/092V)
* [The Stacks Project, Tag 092W](https://stacks.math.columbia.edu/tag/092W)
* [Olivier, *Anneaux absolument plats universels et épimorphismes à buts réduits*][Olivier-AF]
-/

universe u v w u₁ u₂ u₃ u₄

/-- A commutative ring has weak dimension at most one if every finitely generated ideal is
flat. This is condition (3) of Stacks Project, Tag 092S. -/
def HasWeakDimensionLEOne (A : Type u) [CommRing A] : Prop :=
  ∀ I : Ideal A, I.FG → Module.Flat A I

section ProductsOfValuationRings

private theorem flat_fg_ideal_pi
    (J : Type v) (A : J → Type u)
    [∀ j, CommRing (A j)] [∀ j, IsDomain (A j)] [∀ j, ValuationRing (A j)]
    (I : Ideal (∀ j, A j)) (hI : I.FG) : Module.Flat (∀ j, A j) I := by
  classical
  let R := ∀ j, A j
  obtain ⟨S, hSfin, hS⟩ := Submodule.fg_def.mp hI
  let : Fintype S := hSfin.fintype
  let C (j : J) : Ideal (A j) := Ideal.span (Set.range fun x : S ↦ x.1 j)
  have hC (j : J) : (C j).IsPrincipal :=
    IsBezout.isPrincipal_of_FG _ (Submodule.fg_span (Set.finite_range _))
  choose f hf using fun j ↦ (hC j).1
  have hfmem (j : J) : f j ∈ C j := by
    rw [hf j]
    exact Ideal.subset_span (Set.mem_singleton _)
  have hfrepr : ∀ j, ∃ c : S → A j, ∑ x, c x * x.1 j = f j := by
    intro j
    simpa only [C, smul_eq_mul] using
      (Submodule.mem_span_range_iff_exists_fun (R := A j) (v := fun x : S ↦ x.1 j)).mp
        (hfmem j)
  choose c hc using hfrepr
  have hfI : f ∈ I := by
    rw [← hS]
    refine (Submodule.mem_span_iff_of_fintype (R := R) (s := S)).mpr ⟨fun x j ↦ c j x, ?_⟩
    funext j
    rw [Finset.sum_apply]
    change (∑ x, c j x * x.1 j) = f j
    exact hc j
  have hSI : S ⊆ Ideal.span {f} := by
    intro x hx
    have hxC (j : J) : x j ∈ C j :=
      Ideal.subset_span ⟨⟨x, hx⟩, rfl⟩
    have hxspan (j : J) : x j ∈ Ideal.span {f j} := by simpa [hf j] using hxC j
    choose a ha using fun j ↦ Ideal.mem_span_singleton'.mp (hxspan j)
    exact Ideal.mem_span_singleton'.mpr ⟨a, funext ha⟩
  have hprincipal : I = Ideal.span {f} := by
    rw [← hS]
    apply le_antisymm
    · exact Submodule.span_le.mpr hSI
    · exact Ideal.span_le.2 fun _ h ↦ Set.mem_singleton_iff.mp h ▸ (hS ▸ hfI)
  let e : R := fun j ↦ if f j = 0 then 0 else 1
  let g : R := fun j ↦ if f j = 0 then 1 else f j
  have hge : g * e = f := by
    change (fun j ↦ (if f j = 0 then 1 else f j) * (if f j = 0 then 0 else 1)) = f
    funext j
    split_ifs with h <;> simp [h]
  have hg : ∀ x : R, g * x = 0 → x = 0 := by
    intro x hx
    funext j
    have hj := congr_fun hx j
    change (if f j = 0 then 1 else f j) * x j = 0 at hj
    by_cases h : f j = 0
    · change x j = (0 : A j)
      simpa [h] using hj
    · exact (mul_eq_zero.mp hj).resolve_left (by
        change (if f j = 0 then 1 else f j) ≠ 0
        simp [h])
  let E : Ideal R := Ideal.span {e}
  let m : E →ₗ[R] I :=
    LinearMap.codRestrict I ((LinearMap.mulLeft R g).comp E.subtype) (fun x ↦ by
      change g * x.1 ∈ I
      rw [hprincipal]
      obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp x.2
      apply Ideal.mem_span_singleton'.mpr
      refine ⟨a, ?_⟩
      calc
        a * f = a * (g * e) := by rw [hge]
        _ = g * (a * e) := by ring
        _ = g * x.1 := by rw [ha])
  have hm_inj : Function.Injective m := by
    intro x y hxy
    apply Subtype.ext
    apply sub_eq_zero.mp
    apply hg (x.1 - y.1)
    rw [mul_sub, sub_eq_zero]
    simpa [m] using congr_arg Subtype.val hxy
  have hm_surj : Function.Surjective m := by
    intro x
    have xmem : x.1 ∈ Ideal.span {f} := hprincipal ▸ x.2
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp xmem
    let y : E := ⟨a * e, Ideal.mem_span_singleton'.mpr ⟨a, rfl⟩⟩
    refine ⟨y, Subtype.ext ?_⟩
    simp only [m, y, LinearMap.codRestrict_apply, LinearMap.comp_apply,
      LinearMap.mulLeft_apply, Submodule.coe_subtype]
    calc
      g * (a * e) = a * (g * e) := by ring
      _ = a * f := by rw [hge]
      _ = x.1 := ha
  have hE : Module.Flat R E := by
    let inc : E →ₗ[R] R := E.subtype
    let ret : R →ₗ[R] E := LinearMap.codRestrict E (LinearMap.mulLeft R e) (fun x ↦
      Ideal.mem_span_singleton'.mpr ⟨x, by simp [mul_comm]⟩)
    apply Module.Flat.of_retract inc ret
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    simp only [LinearMap.comp_apply, inc, ret, LinearMap.codRestrict_apply,
      LinearMap.mulLeft_apply, Submodule.coe_subtype, LinearMap.id_apply]
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp x.2
    rw [← ha]
    funext j
    change (if f j = 0 then 0 else 1) *
      (a j * (if f j = 0 then 0 else 1)) = a j * (if f j = 0 then 0 else 1)
    by_cases h : f j = 0 <;> simp [h]
  let iso : E ≃ₗ[R] I := LinearEquiv.ofBijective m ⟨hm_inj, hm_surj⟩
  exact Module.Flat.of_linearEquiv iso.symm

/-- A product of valuation rings has weak dimension at most one, and the product of their
fraction fields is the localization at the componentwise non-zero-divisors. -/
@[stacks 092T]
theorem weakDimensionLE_one_and_isLocalization_pi_fractionRing
    (J : Type v) (A : J → Type u) (K : J → Type w)
    [∀ j, CommRing (A j)] [∀ j, IsDomain (A j)] [∀ j, ValuationRing (A j)]
    [∀ j, Field (K j)] [∀ j, Algebra (A j) (K j)] [∀ j, IsFractionRing (A j) (K j)] :
    HasWeakDimensionLEOne (∀ j, A j) ∧
      IsLocalization
        (.pi Set.univ (fun j ↦ nonZeroDivisors (A j)))
        (∀ j, K j) :=
  ⟨flat_fg_ideal_pi J A, inferInstance⟩

end ProductsOfValuationRings

section IntegralClosure

open scoped TensorProduct

/-- If every finitely generated ideal of `A` is flat, then every submodule of a flat
`A`-module is flat. This is the implication (3) ⟹ (4) of Stacks Tag 092S. -/
theorem flat_submodule_of_flat_of_weakDimensionLE_one
    {A : Type u} {M : Type v} [CommRing A] [AddCommGroup M] [Module A M]
    [Module.Flat A M] (h : HasWeakDimensionLEOne A) (N : Submodule A M) :
    Module.Flat A N := by
  rw [Module.Flat.iff_rTensor_injective]
  intro I hI
  let : Module.Flat A I := h I hI
  let i : N →ₗ[A] M := N.subtype
  refine .of_comp (f := i.lTensor A) ?_
  rw [← LinearMap.coe_comp, LinearMap.lTensor_comp_rTensor]
  exact TensorProduct.map_injective_of_flat_flat' I.subtype i Subtype.val_injective
    Subtype.val_injective

/-- A flat injective epimorphism of commutative rings whose source has weak dimension at most one
makes the source integrally closed in the target. -/
@[stacks 092V]
theorem isIntegrallyClosedIn_of_isEpi_of_flat_of_weakDimensionLE_one
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] [Algebra.IsEpi A B]
    (hA : HasWeakDimensionLEOne A)
    (hinjective : Function.Injective (algebraMap A B)) :
    IsIntegrallyClosedIn A B := by
  rw [isIntegrallyClosedIn_iff]
  refine ⟨hinjective, fun {x} hx ↦ ?_⟩
  let S : Subalgebra A B := Algebra.adjoin A {x}
  let : Module.Flat A S :=
    flat_submodule_of_flat_of_weakDimensionLE_one hA S.toSubmodule
  let f : S →ₗ[A] B := S.val.toLinearMap
  have hf : Function.Injective f := Subtype.val_injective
  have htensor : Function.Injective ((f.lTensor B) ∘ₗ (f.rTensor S)) :=
    (Module.Flat.lTensor_preserves_injective_linearMap f hf).comp
      (Module.Flat.rTensor_preserves_injective_linearMap f hf)
  let : Module.Finite A S := Algebra.finite_adjoin_simple_of_isIntegral hx
  let : Algebra.IsEpi A S := (Algebra.isEpi_iff_forall_one_tmul_eq A S).mpr fun s ↦ by
    apply htensor
    simp [f, Algebra.isEpi_iff_forall_one_tmul_eq A B |>.mp inferInstance]
  obtain ⟨a, ha⟩ :=
    (Algebra.isEpi_iff_surjective_algebraMap_of_finite (R := A) (A := S)).mp inferInstance
      ⟨x, Algebra.subset_adjoin (R := A) (Set.mem_singleton x)⟩
  exact ⟨a, congrArg Subtype.val ha⟩

end IntegralClosure

section NormalDomainSquare

open CategoryTheory

/-- A normal domain and its fraction field fit into a cartesian square whose lower-left ring has
weak dimension at most one and whose lower map is flat, injective, and a ring epimorphism. -/
@[stacks 092U]
theorem exists_isPullback_with_weakDimensionLE_one
    (A : Type u) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K] :
    ∃ (V L : Type (max u v)) (_ : CommRing V) (_ : CommRing L)
      (_ : Algebra A V) (_ : Algebra K L) (_ : Algebra V L)
      (_ : Module.Flat V L) (_ : Algebra.IsEpi V L),
      HasWeakDimensionLEOne V ∧
        Function.Injective (algebraMap V L) ∧
        IsPullback
          (CommRingCat.ofHom (algebraMap A K).ulift)
          (CommRingCat.ofHom
            ((algebraMap A V).comp ULift.ringEquiv.toRingHom))
          (CommRingCat.ofHom
            ((algebraMap K L).comp ULift.ringEquiv.toRingHom))
          (CommRingCat.ofHom (algebraMap V L)) := by
  let J := { x : ULift.{u} K // x.down ∉ integralClosure A K }
  let W : J → ValuationSubring K := fun x =>
    Classical.choose (Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn
      (x := x.1.down) (R := (integralClosure A K).toSubring) x.property)
  have hW (x : J) := Classical.choose_spec
    (Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn
      (x := x.1.down) (R := (integralClosure A K).toSubring) x.property)
  let V := ∀ x : J, W x
  let L := ∀ _x : J, K
  let (x : J) : Algebra A (W x) := RingHom.toAlgebra
    ((algebraMap A K).codRestrict (W x) fun a => (hW x).1 ((integralClosure A K).algebraMap_mem a))
  let : Algebra A V := Pi.algebra _ _
  let : Algebra K L := Pi.algebra _ _
  let : Algebra V L := RingHom.toAlgebra
    { toFun := fun f x => (f x : K)
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hloc := weakDimensionLE_one_and_isLocalization_pi_fractionRing J
    (fun x => W x) (fun _x => K)
  let M := Submonoid.pi Set.univ (fun x : J => nonZeroDivisors (W x))
  let : IsLocalization M L := hloc.2
  let : Module.Flat V L := IsLocalization.flat L M
  let : Algebra.IsEpi V L := CommRingCat.epi_iff_epi.mp (IsLocalization.epi M L)
  refine ⟨V, L, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, hloc.1, ?_, ?_⟩
  · exact fun _ _ e ↦ funext fun x ↦ Subtype.ext (congr_fun e x)
  · let e : A ≃+* RingHom.range (algebraMap A K) := RingEquiv.ofBijective
      (algebraMap A K).rangeRestrict
      ⟨fun _ _ h => IsFractionRing.injective A K (congr_arg Subtype.val h), fun y => by
        obtain ⟨a, ha⟩ := y.property
        exact ⟨a, Subtype.ext ha⟩⟩
    let toK (s : Limits.PullbackCone
        (CommRingCat.ofHom ((algebraMap K L).comp ULift.ringEquiv.toRingHom))
        (CommRingCat.ofHom (algebraMap V L))) : s.pt →+* K :=
      ULift.ringEquiv.toRingHom.comp s.fst.hom
    have hcond (s : Limits.PullbackCone
        (CommRingCat.ofHom ((algebraMap K L).comp ULift.ringEquiv.toRingHom))
        (CommRingCat.ofHom (algebraMap V L))) (z : s.pt) (x : J) :
        toK s z = (s.snd.hom z x : K) :=
      congr_fun (RingHom.congr_fun (congrArg CommRingCat.Hom.hom s.condition) z) x
    have toK_mem (s : Limits.PullbackCone
        (CommRingCat.ofHom ((algebraMap K L).comp ULift.ringEquiv.toRingHom))
        (CommRingCat.ofHom (algebraMap V L))) (z : s.pt) :
        toK s z ∈ RingHom.range (algebraMap A K) := by
      rw [RingHom.mem_range]
      apply (isIntegrallyClosed_iff K).mp (by infer_instance)
      rw [← mem_integralClosure_iff]
      by_contra hz
      let x : J := ⟨ULift.up (toK s z), hz⟩
      apply (hW x).2
      have he := hcond s z x
      change toK s z ∈ W x
      exact he.symm ▸ (s.snd.hom z x).property
    let toRange (s : Limits.PullbackCone
        (CommRingCat.ofHom ((algebraMap K L).comp ULift.ringEquiv.toRingHom))
        (CommRingCat.ofHom (algebraMap V L))) :
        s.pt →+* RingHom.range (algebraMap A K) := (toK s).codRestrict _ (toK_mem s)
    let lift (s : Limits.PullbackCone
        (CommRingCat.ofHom ((algebraMap K L).comp ULift.ringEquiv.toRingHom))
        (CommRingCat.ofHom (algebraMap V L))) : s.pt ⟶ CommRingCat.of (ULift A) :=
      CommRingCat.ofHom
        (ULift.ringEquiv.symm.toRingHom.comp (e.symm.toRingHom.comp (toRange s)))
    refine { w := ?_, isLimit' := ⟨?_⟩ }
    · ext a x
      rfl
    · refine Limits.PullbackCone.IsLimit.mk (by ext a x; rfl) lift ?_ ?_ ?_
      · intro s
        ext z
        exact congr_arg Subtype.val (e.apply_symm_apply (toRange s z))
      · intro s
        ext z x
        change algebraMap A K _ = _
        rw [show algebraMap A K _ = toK s z by
          exact congr_arg Subtype.val (e.apply_symm_apply (toRange s z))]
        exact hcond s z x
      · intro s m hm₁ _hm₂
        apply CommRingCat.hom_ext
        apply RingHom.ext
        intro z
        apply ULift.ext
        apply IsFractionRing.injective A K
        change algebraMap A K ((m.hom z).down) = algebraMap A K ((lift s).hom z).down
        rw [show algebraMap A K ((lift s).hom z).down = toK s z by
          exact congr_arg Subtype.val (e.apply_symm_apply (toRange s z))]
        exact congr_arg (fun q => (q.hom z).down) hm₁

end NormalDomainSquare

section FractionFieldBaseChange

open CategoryTheory CategoryTheory.MonoidalCategory TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Weak dimension at most one is inherited by a weakly étale algebra: an ideal of `B` is an
`A`-submodule of the flat `A`-module `B`, hence flat over `A` by Stacks 092S (3) ⟹ (4), hence
flat over `B` by Stacks 092C. -/
private theorem weakDimensionLEOne_of_weaklyEtale
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    (hA : HasWeakDimensionLEOne A) (hAB : Algebra.WeaklyEtale A B) :
    HasWeakDimensionLEOne B := by
  let : Algebra.WeaklyEtale A B := hAB
  intro I _
  have hIA : Module.Flat A (I.restrictScalars A) :=
    flat_submodule_of_flat_of_weakDimensionLE_one hA (I.restrictScalars A)
  exact flat_of_flat_of_mul_flat A B (Algebra.WeaklyEtale.flat_lmul' A B) I hIA

private theorem closed_top_of_pullback
    {R S T U : Type u} [CommRing R] [CommRing S] [CommRing T] [CommRing U]
    [Algebra R S] [Algebra R T] [Algebra S U] [Algebra T U] [Algebra R U]
    [IsScalarTower R S U] [IsScalarTower R T U]
    (hsq : IsPullback
      (CommRingCat.ofHom (algebraMap R S)) (CommRingCat.ofHom (algebraMap R T))
      (CommRingCat.ofHom (algebraMap S U)) (CommRingCat.ofHom (algebraMap T U)))
    (hT : IsIntegrallyClosedIn T U) : IsIntegrallyClosedIn R S := by
  rw [isIntegrallyClosedIn_iff] at hT ⊢
  have hsq' := hsq.map (CategoryTheory.forget CommRingCat)
  constructor
  · intro x y hxy
    have hw (z : R) : algebraMap S U (algebraMap R S z) =
        algebraMap T U (algebraMap R T z) :=
      congrArg (fun q : CommRingCat.of R ⟶ CommRingCat.of U ↦ q.hom z) hsq.w
    have hRT := hT.1 ((hw x).symm.trans ((congrArg (algebraMap S U) hxy).trans (hw y)))
    exact congrArg (fun q ↦ q 0) (hsq'.hom_ext (W := R)
      (k := TypeCat.ofHom fun _ : R ↦ x) (l := TypeCat.ofHom fun _ : R ↦ y)
      (by apply ConcreteCategory.hom_ext; intro; simpa using hxy)
      (by apply ConcreteCategory.hom_ext; intro; simpa using hRT))
  · intro x hx
    have hx' : IsIntegral T (algebraMap S U x) :=
      (hx.map (IsScalarTower.toAlgHom R S U)).tower_top
    obtain ⟨y, hy⟩ := hT.2 hx'
    let sx : S ⟶ (forget CommRingCat).obj (CommRingCat.of S) := TypeCat.ofHom fun _ ↦ x
    let ty : S ⟶ (forget CommRingCat).obj (CommRingCat.of T) := TypeCat.ofHom fun _ ↦ y
    have hw : sx ≫ (forget CommRingCat).map (CommRingCat.ofHom (algebraMap S U)) =
        ty ≫ (forget CommRingCat).map (CommRingCat.ofHom (algebraMap T U)) := by
      apply ConcreteCategory.hom_ext
      intro
      simpa [sx, ty] using hy.symm
    exact ⟨hsq'.lift sx ty hw 0,
      congrArg (fun q ↦ (ConcreteCategory.hom q) 0) (hsq'.lift_fst sx ty hw)⟩

private theorem tensor_isPullback
    {A B K V L : Type u} [CommRing A] [CommRing B] [CommRing K] [CommRing V]
    [CommRing L] [Algebra A B] [Algebra A K] [Algebra A V]
    [Algebra K L] [Algebra V L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A V L] [Module.Flat A B]
    (hsq : IsPullback
      (CommRingCat.ofHom (algebraMap A K)) (CommRingCat.ofHom (algebraMap A V))
      (CommRingCat.ofHom (algebraMap K L)) (CommRingCat.ofHom (algebraMap V L))) :
    IsPullback
      ((CommRingCat.tensorProd (CommRingCat.of A) (CommRingCat.of B)).map
        (Algebra.ofId A K).toUnder)
      ((CommRingCat.tensorProd (CommRingCat.of A) (CommRingCat.of B)).map
        (Algebra.ofId A V).toUnder)
      ((CommRingCat.tensorProd (CommRingCat.of A) (CommRingCat.of B)).map
        (IsScalarTower.toAlgHom A K L).toUnder)
      ((CommRingCat.tensorProd (CommRingCat.of A) (CommRingCat.of B)).map
        (IsScalarTower.toAlgHom A V L).toUnder) := by
  let f : CommRingCat.mkUnder (CommRingCat.of A) A ⟶ CommRingCat.mkUnder (CommRingCat.of A) K :=
    (Algebra.ofId A K).toUnder
  let g : CommRingCat.mkUnder (CommRingCat.of A) A ⟶ CommRingCat.mkUnder (CommRingCat.of A) V :=
    (Algebra.ofId A V).toUnder
  let h : CommRingCat.mkUnder (CommRingCat.of A) K ⟶ CommRingCat.mkUnder (CommRingCat.of A) L :=
    (IsScalarTower.toAlgHom A K L).toUnder
  let i : CommRingCat.mkUnder (CommRingCat.of A) V ⟶ CommRingCat.mkUnder (CommRingCat.of A) L :=
    (IsScalarTower.toAlgHom A V L).toUnder
  have hUnder : IsPullback f g h i := by
    apply IsPullback.of_map (Under.forget (CommRingCat.of A)) (by ext; simp [f, g, h, i])
    change IsPullback
      (CommRingCat.ofHom (algebraMap A K)) (CommRingCat.ofHom (algebraMap A V))
      (CommRingCat.ofHom (algebraMap K L)) (CommRingCat.ofHom (algebraMap V L))
    exact hsq
  exact hUnder.map (CommRingCat.tensorProd (CommRingCat.of A) (CommRingCat.of B))

private theorem closed_equiv
    {R : Type u₁} {S : Type u₂} {R' : Type u₃} {S' : Type u₄}
    [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    [Algebra R S] [Algebra R' S'] (eR : R ≃+* R') (eS : S ≃+* S')
    (hcomm : (algebraMap R' S').comp eR.toRingHom =
      eS.toRingHom.comp (algebraMap R S))
    (h : IsIntegrallyClosedIn R S) : IsIntegrallyClosedIn R' S' := by
  have hc (r : R) : algebraMap R' S' (eR r) = eS (algebraMap R S r) := by
    change (algebraMap R' S').comp eR.toRingHom r =
      eS.toRingHom.comp (algebraMap R S) r
    exact RingHom.congr_fun hcomm r
  have hc' (x : R') : eS (algebraMap R S (eR.symm x)) = algebraMap R' S' x := by
    simpa only [eR.apply_symm_apply] using (hc (eR.symm x)).symm
  rw [isIntegrallyClosedIn_iff] at h ⊢
  constructor
  · intro x y hxy
    rw [← eR.apply_symm_apply x, ← eR.apply_symm_apply y]
    congr 1
    apply h.1
    apply eS.injective
    exact (hc' x).trans (hxy.trans (hc' y).symm)
  · intro x hx
    have hx' : IsIntegral R (eS.symm x) :=
      IsIntegral.map_of_comp_eq eR.symm.toRingHom eS.symm.toRingHom (by
        ext r'
        apply eS.injective
        simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe]
        exact (hc' r').trans (eS.apply_symm_apply _).symm) hx
    obtain ⟨r, hr⟩ := h.2 hx'
    refine ⟨eR r, ?_⟩
    calc
      algebraMap R' S' (eR r) = eS (algebraMap R S r) := hc r
      _ = eS (eS.symm x) := congrArg eS hr
      _ = x := eS.apply_symm_apply x

private def tensorProductRingEquivOfAlgebraEq
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (a b : Algebra R S) [Algebra R T] (h : a = b) :
    (letI := a; S ⊗[R] T) ≃+* (letI := b; S ⊗[R] T) := by
  subst b
  exact RingEquiv.refl _

private theorem tensorProductRingEquivOfAlgebraEq_tmul
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (a b : Algebra R S) [Algebra R T] (h : a = b) (s : S) (t : T) :
    tensorProductRingEquivOfAlgebraEq a b h
        (letI := a; s ⊗ₜ[R] t) = (letI := b; s ⊗ₜ[R] t) := by
  subst b
  rfl

private theorem core
    (A B K : Type u) [CommRing A] [CommRing B] [Field K]
    [Algebra A B] [Algebra A K] [IsDomain A] [IsIntegrallyClosed A]
    [IsFractionRing A K] (hAB : Algebra.WeaklyEtale A B) :
    IsIntegrallyClosedIn B (B ⊗[A] K) := by
  let := hAB
  obtain ⟨V, L, iV, iL, iAV, iKL, iVL, iFlat, iEpi, hV, hinj, hpull⟩ :=
    exists_isPullback_with_weakDimensionLE_one A K
  let : CommRing V := iV
  let : CommRing L := iL
  let : Algebra A V := iAV
  let : Algebra K L := iKL
  let : Algebra V L := iVL
  let : Module.Flat V L := iFlat
  let : Algebra.IsEpi V L := iEpi
  let : Algebra A L := RingHom.toAlgebra ((algebraMap V L).comp (algebraMap A V))
  let : IsScalarTower A V L := IsScalarTower.of_algebraMap_eq' rfl
  let AU := ULift.{u} A
  let BU := ULift.{u} B
  let KU := ULift.{u} K
  let : Algebra AU BU := ULift.algebra' A BU
  let : Algebra AU KU := ULift.algebra' A KU
  let : Algebra AU V := ULift.algebra' A V
  let : Algebra KU L := ULift.algebra' K L
  let : Algebra AU L := ULift.algebra' A L
  let : IsScalarTower AU V L := IsScalarTower.of_algebraMap_eq' rfl
  have hcomm : (algebraMap KU L).comp (algebraMap AU KU) = algebraMap AU L :=
    congrArg CommRingCat.Hom.hom hpull.w
  let : IsScalarTower AU KU L := IsScalarTower.of_algebraMap_eq' hcomm.symm
  have hBU : Algebra.WeaklyEtale AU BU := Algebra.WeaklyEtale.ulift_iff.mpr hAB
  let := hBU
  have hPB := tensor_isPullback (A := AU) (B := BU) (K := KU) (V := V) (L := L) hpull
  let mapLeft {X Y : Type u} [CommRing X] [CommRing Y] [Algebra AU X] [Algebra AU Y]
      (f : X →ₐ[AU] Y) : BU ⊗[AU] X →ₐ[BU] BU ⊗[AU] Y :=
    Algebra.TensorProduct.map (AlgHom.id BU BU) f
  have hPBring := hPB.map (Under.forget (CommRingCat.of BU))
  let mapRight {X Y : Under (CommRingCat.of AU)} (f : X ⟶ Y) :=
    let : Algebra AU X.right := CommRingCat.instAlgebraCarrierRight X
    let : Algebra AU Y.right := CommRingCat.instAlgebraCarrierRight Y
    (Algebra.TensorProduct.map (CommRingCat.toAlgHom f) (AlgHom.id AU BU)).toRingHom
  let e (X : Under (CommRingCat.of AU)) :=
    let : Algebra AU X.right := CommRingCat.instAlgebraCarrierRight X
    (Algebra.TensorProduct.comm AU BU X.right).toRingEquiv.toCommRingCatIso
  let Ao := CommRingCat.mkUnder (CommRingCat.of AU) AU
  let Ko := CommRingCat.mkUnder (CommRingCat.of AU) KU
  let Vo := CommRingCat.mkUnder (CommRingCat.of AU) V
  let Lo := CommRingCat.mkUnder (CommRingCat.of AU) L
  let fAK : Ao ⟶ Ko := (Algebra.ofId AU KU).toUnder
  let fAV : Ao ⟶ Vo := (Algebra.ofId AU V).toUnder
  let fKL : Ko ⟶ Lo := (IsScalarTower.toAlgHom AU KU L).toUnder
  let fVL : Vo ⟶ Lo := (IsScalarTower.toAlgHom AU V L).toUnder
  have he {X Y : Under (CommRingCat.of AU)} (f : X ⟶ Y) :
      (Under.forget (CommRingCat.of BU)).map
          ((CommRingCat.tensorProd (CommRingCat.of AU) (CommRingCat.of BU)).map f) ≫
          (e Y).hom =
        (e X).hom ≫ CommRingCat.ofHom (mapRight f) := by
    let : Algebra AU X.right := CommRingCat.instAlgebraCarrierRight X
    let : Algebra AU Y.right := CommRingCat.instAlgebraCarrierRight Y
    change CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id BU BU)
        (CommRingCat.toAlgHom f)).toRingHom ≫ (e Y).hom =
      (e X).hom ≫ CommRingCat.ofHom (mapRight f)
    ext x <;> rfl
  have hright : IsPullback
      (CommRingCat.ofHom (mapRight fAK))
      (CommRingCat.ofHom (mapRight fAV))
      (CommRingCat.ofHom (mapRight fKL))
      (CommRingCat.ofHom (mapRight fVL)) :=
    hPBring.of_iso (e Ao) (e Ko) (e Vo) (e Lo)
    (he fAK) (he fAV) (he fKL) (he fVL)
  let : Algebra AU Ao.right := CommRingCat.instAlgebraCarrierRight Ao
  let : Algebra AU Ko.right := CommRingCat.instAlgebraCarrierRight Ko
  let : Algebra AU Vo.right := CommRingCat.instAlgebraCarrierRight Vo
  let : Algebra AU Lo.right := CommRingCat.instAlgebraCarrierRight Lo
  let R0 := Ao.right ⊗[AU] BU
  let S0 := Ko.right ⊗[AU] BU
  let T0 := Vo.right ⊗[AU] BU
  let U0 := Lo.right ⊗[AU] BU
  let : CommRing R0 := inferInstanceAs (CommRing (Ao.right ⊗[AU] BU))
  let : CommRing S0 := inferInstanceAs (CommRing (Ko.right ⊗[AU] BU))
  let : CommRing T0 := inferInstanceAs (CommRing (Vo.right ⊗[AU] BU))
  let : CommRing U0 := inferInstanceAs (CommRing (Lo.right ⊗[AU] BU))
  let : Algebra R0 S0 := RingHom.toAlgebra (mapRight fAK)
  let : Algebra R0 T0 := RingHom.toAlgebra (mapRight fAV)
  let : Algebra S0 U0 := RingHom.toAlgebra (mapRight fKL)
  let : Algebra T0 U0 := RingHom.toAlgebra (mapRight fVL)
  have hdim := weakDimensionLEOne_of_weaklyEtale Vo T0 hV inferInstance
  have hflatMap : (mapRight fVL).Flat := by
    change (Algebra.TensorProduct.map (CommRingCat.toAlgHom fVL)
      (AlgHom.id AU BU)).toRingHom.Flat
    have hf : (CommRingCat.toAlgHom fVL).toRingHom.Flat :=
      (RingHom.flat_algebraMap_iff.mpr iFlat : (algebraMap V L).Flat)
    exact RingHom.Flat.tensorProductMap
      (f := CommRingCat.toAlgHom fVL) (g := AlgHom.id AU BU)
      hf (RingHom.Flat.of_bijective Function.bijective_id)
  let : Module.Flat T0 U0 := hflatMap
  have hinj' : Function.Injective (mapRight fVL) := by
    have hi : Function.Injective (CommRingCat.toAlgHom fVL) := by
      change Function.Injective (algebraMap V L)
      exact hinj
    have ht := Module.Flat.rTensor_preserves_injective_linearMap (M := BU)
      (CommRingCat.toAlgHom fVL).toLinearMap hi
    have heq : (Algebra.TensorProduct.map (CommRingCat.toAlgHom fVL)
        (AlgHom.id AU BU)).toLinearMap =
        LinearMap.rTensor BU (CommRingCat.toAlgHom fVL).toLinearMap := by
      ext
      rfl
    rwa [← heq] at ht
  have hepi : Algebra.IsEpi T0 U0 := by
    have : Epi fVL.right := CommRingCat.epi_iff_epi.mpr
      (inferInstanceAs (Algebra.IsEpi V L))
    let : Epi fVL := Under.epi_of_epi_right fVL
    let F := CommRingCat.tensorProd (CommRingCat.of AU) (CommRingCat.of BU)
    let G := Under.pushout (CommRingCat.ofHom (algebraMap AU BU))
    let α := CommRingCat.tensorProdIsoPushout (CommRingCat.of AU) (CommRingCat.of BU)
    have : Epi (G.map fVL) := by dsimp [G]; infer_instance
    have : Epi (F.map fVL) := by
      constructor
      intro Z a b hab
      apply (cancel_epi (α.app _).inv).mp
      apply (cancel_epi (G.map fVL)).mp
      have hn := α.inv.naturality fVL
      change G.map fVL ≫ (α.app Lo).inv =
        (α.app Vo).inv ≫ F.map fVL at hn
      calc
        G.map fVL ≫ (α.app Lo).inv ≫ a =
            (α.app Vo).inv ≫ F.map fVL ≫ a := by
          rw [← Category.assoc, hn, Category.assoc]
        _ = (α.app Vo).inv ≫ F.map fVL ≫ b := by rw [hab]
        _ = G.map fVL ≫ (α.app Lo).inv ≫ b := by
          simpa only [Category.assoc] using congrArg (fun q ↦ q ≫ b) hn.symm
    let : IsIso (e Lo).hom := by dsimp [e]; infer_instance
    let : IsIso (e Vo).hom := by dsimp [e]; infer_instance
    have : Epi (CommRingCat.ofHom (mapRight fVL)) := by
      constructor
      intro Z a b hab
      apply (cancel_epi (e Lo).hom).mp
      apply (cancel_epi (F.map fVL).right).mp
      change ((Under.forget (CommRingCat.of BU)).map
          ((CommRingCat.tensorProd (CommRingCat.of AU) (CommRingCat.of BU)).map fVL) ≫
          (e Lo).hom) ≫ a =
        ((Under.forget (CommRingCat.of BU)).map
          ((CommRingCat.tensorProd (CommRingCat.of AU) (CommRingCat.of BU)).map fVL) ≫
          (e Lo).hom) ≫ b
      rw [he fVL]
      change (e Vo).hom ≫ (CommRingCat.ofHom (mapRight fVL) ≫ a) =
        (e Vo).hom ≫ (CommRingCat.ofHom (mapRight fVL) ≫ b)
      exact congrArg (fun q ↦ (e Vo).hom ≫ q) hab
    exact CommRingCat.epi_iff_epi.mp inferInstance
  let : Algebra.IsEpi T0 U0 := hepi
  let : Algebra R0 U0 := RingHom.toAlgebra ((mapRight fVL).comp (mapRight fAV))
  let : IsScalarTower R0 T0 U0 := IsScalarTower.of_algebraMap_eq' rfl
  have hsqMaps : (mapRight fKL).comp (mapRight fAK) =
      (mapRight fVL).comp (mapRight fAV) :=
    congrArg CommRingCat.Hom.hom hright.w
  let : IsScalarTower R0 S0 U0 := IsScalarTower.of_algebraMap_eq' hsqMaps.symm
  let eR : R0 ≃+* B := by
    change (AU ⊗[AU] BU) ≃+* B
    exact (Algebra.TensorProduct.lid AU BU).toRingEquiv.trans ULift.ringEquiv
  have hKo : (CommRingCat.instAlgebraCarrierRight Ko : Algebra AU Ko.right) =
      ULift.algebra' A KU := by
    apply Algebra.algebra_ext
    intro r
    rfl
  let eInst : S0 ≃+* (KU ⊗[AU] BU) := by
    dsimp [S0, Ko]
    exact tensorProductRingEquivOfAlgebraEq _ _ hKo
  let eu : ULift.{u} (B ⊗[A] K) ≃+* (BU ⊗[AU] KU) :=
    (Algebra.TensorProduct.uliftEquiv A A B K).toRingEquiv
  have eu_down (x : BU) (y : KU) : ULift.ringEquiv (eu.symm (x ⊗ₜ[AU] y)) =
      x.down ⊗ₜ[A] y.down := rfl
  let eS : S0 ≃+* (B ⊗[A] K) := eInst.trans
    ((Algebra.TensorProduct.comm AU KU BU).toRingEquiv.trans (eu.symm.trans ULift.ringEquiv))
  have eInst_tmul (x : BU) : eInst (1 ⊗ₜ[AU] x) = 1 ⊗ₜ[AU] x := by
    dsimp [eInst, S0, Ko]
    exact tensorProductRingEquivOfAlgebraEq_tmul _ _ hKo 1 x
  have eInst_tmul_left (x : Ko.right) :=
    tensorProductRingEquivOfAlgebraEq_tmul
      (CommRingCat.instAlgebraCarrierRight Ko : Algebra AU Ko.right)
      (ULift.algebra' A KU) hKo x (1 : BU)
  have mapRight_fAK_tmul (x : Ao.right) :
      mapRight fAK (x ⊗ₜ[AU] (1 : BU)) =
        (CommRingCat.toAlgHom fAK x) ⊗ₜ[AU] (1 : BU) := rfl
  apply closed_equiv eR eS
  · change (algebraMap B (B ⊗[A] K)).comp eR.toRingHom =
      eS.toRingHom.comp (mapRight fAK)
    ext x
    · change algebraMap B (B ⊗[A] K) (eR (x ⊗ₜ[AU] (1 : BU))) =
        eS (mapRight fAK (x ⊗ₜ[AU] (1 : BU)))
      rw [mapRight_fAK_tmul]
      simp only [eS, RingEquiv.trans_apply]
      have he := eInst_tmul_left (CommRingCat.toAlgHom fAK x)
      change eInst ((CommRingCat.toAlgHom fAK x) ⊗ₜ[AU] (1 : BU)) = _ at he
      rw [he]
      convert Algebra.TensorProduct.tmul_one_eq_one_tmul (A := B) (B := K) x.down using 1
      · have hv : eR (x ⊗ₜ[AU] (1 : BU)) = algebraMap A B x.down := by
          change ULift.ringEquiv (Algebra.TensorProduct.lid AU BU (x ⊗ₜ[AU] 1)) =
          algebraMap A B x.down
          rw [Algebra.TensorProduct.lid_tmul]
          change (SMul.smul (self := inferInstanceAs (SMul AU BU)) (x : AU) (1 : BU)).down =
            algebraMap A B x.down
          change (x.down • (1 : B)) = algebraMap A B x.down
          simp [Algebra.smul_def]
        rw [hv]
        rfl
      · exact eu_down (1 : BU) (CommRingCat.toAlgHom fAK x)
    · change algebraMap B (B ⊗[A] K) (eR (1 ⊗ₜ[AU] x)) =
        eS (mapRight fAK (1 ⊗ₜ[AU] x))
      have hv : eR (1 ⊗ₜ[AU] x) = x.down := by
        change ULift.ringEquiv (Algebra.TensorProduct.lid AU BU (1 ⊗ₜ[AU] x)) = x.down
        rw [Algebra.TensorProduct.lid_tmul, one_smul]
        rfl
      rw [hv]
      simp only [eS, RingEquiv.trans_apply]
      have hm : mapRight fAK (1 ⊗ₜ[AU] x) = 1 ⊗ₜ[AU] x := by
        simp [mapRight, fAK, Ao, Ko]
      rw [hm, eInst_tmul]
      exact (eu_down x (1 : KU)).symm
  · exact closed_top_of_pullback hright
      (isIntegrallyClosedIn_of_isEpi_of_flat_of_weakDimensionLE_one (A := T0) (B := U0) hdim hinj')

/-- A weakly étale algebra over a normal domain is integrally closed in its scalar extension
to any fraction field of the domain. -/
@[stacks 092W]
theorem isIntegrallyClosedIn_tensorProduct_fractionField_of_weaklyEtale
    (A : Type u) (B : Type v) (K : Type w)
    [CommRing A] [CommRing B] [Field K] [Algebra A B] [Algebra A K]
    [IsDomain A] [IsIntegrallyClosed A] [IsFractionRing A K]
    (hAB : Algebra.WeaklyEtale A B) :
    IsIntegrallyClosedIn B (B ⊗[A] K) := by
  let AU := ULift.{max u (max v w)} A
  let BU := ULift.{max u (max v w)} B
  let KU := ULift.{max u (max v w)} K
  let : Algebra AU BU := ULift.algebra' A BU
  let : Algebra AU KU := ULift.algebra' A KU
  let : IsCancelMulZero AU :=
    { mul_left_cancel_of_ne_zero := by
        intro a ha b c h
        apply ULift.down_injective
        apply mul_left_cancel₀ (a := a.down)
        · exact fun ha0 ↦ ha (ULift.down_injective ha0)
        · exact congrArg ULift.down h
      mul_right_cancel_of_ne_zero := by
        intro a ha b c h
        apply ULift.down_injective
        apply mul_right_cancel₀ (b := a.down)
        · exact fun ha0 ↦ ha (ULift.down_injective ha0)
        · exact congrArg ULift.down h }
  let : IsDomain AU := ⟨⟩
  let : IsIntegrallyClosed AU := IsIntegrallyClosed.of_equiv ULift.ringEquiv.symm
  let : Algebra A KU := ULift.algebra
  let : IsFractionRing A KU :=
    IsFractionRing.of_algEquiv (ULift.algEquiv (R := A)).symm
  let : IsFractionRing AU KU :=
    IsFractionRing.of_ringEquiv_left ULift.ringEquiv (by intro; rfl)
  have hBU : Algebra.WeaklyEtale AU BU := Algebra.WeaklyEtale.ulift_iff.mpr hAB
  have h := core AU BU KU hBU
  let eB : BU ≃+* B := ULift.ringEquiv
  let eu : ULift.{max u (max v w)} (B ⊗[A] K) ≃+* (BU ⊗[AU] KU) :=
    (Algebra.TensorProduct.uliftEquiv A A B K).toRingEquiv
  let eT : (BU ⊗[AU] KU) ≃+* (B ⊗[A] K) := eu.symm.trans ULift.ringEquiv
  have eu_down (x : BU) (y : KU) : ULift.ringEquiv (eu.symm (x ⊗ₜ[AU] y)) =
      x.down ⊗ₜ[A] y.down := rfl
  apply closed_equiv eB eT
  · ext x
    exact (eu_down x (1 : KU)).symm
  · exact h

end FractionFieldBaseChange
