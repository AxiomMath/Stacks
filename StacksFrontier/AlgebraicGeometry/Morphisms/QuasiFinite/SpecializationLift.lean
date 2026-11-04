module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.SurjectiveOnStalks
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.RingHom.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Criteria
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.SpecializationTrdeg

/-!
# Two lifts of a specialization over a field agree

Let `g : V ⟶ Spec k` be locally of finite type over a field and let `a, b : W ⟶ V` be two
morphisms with the same composite to `Spec k`. If `a w` specializes to `b w` and the residue
field of `w` is algebraic over the residue field of `b w`, then the two points coincide.

## Main results

* `AlgebraicGeometry.residueField_finite_of_quasiFiniteAt`: a morphism quasi-finite on stalks at
  a point induces a finite residue field extension there.
* `AlgebraicGeometry.residueField_finite_of_locallyQuasiFinite`: the same at every point of a
  locally quasi-finite morphism.
* `AlgebraicGeometry.residueFieldMap_finite_of_surjectiveOnStalks`: a morphism surjective on
  stalks induces a surjective, hence finite, residue field extension.
* `AlgebraicGeometry.eq_of_specialization_of_common_lift_of_isAlgebraic`: two lifts of a
  specialization over a field agree, under an algebraicity hypothesis on the special one.
* `AlgebraicGeometry.eq_of_specialization_of_common_lift_over_field`: its locally quasi-finite
  case.
* `AlgebraicGeometry.forall_quasiFiniteAt_of_specialization_eq`: a morphism locally of finite
  type whose source has no nontrivial specialization is quasi-finite at every point.

## References

* [Stacks Project, Tag 01TG](https://stacks.math.columbia.edu/tag/01TG)
* [Stacks Project, Tag 06RU](https://stacks.math.columbia.edu/tag/06RU)
* [Stacks Project, Tag 06UC](https://stacks.math.columbia.edu/tag/06UC)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- At a point where a morphism is quasi-finite on stalks the residue field extension is
finite. -/
public theorem residueField_finite_of_quasiFiniteAt {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    (hx : (f.stalkMap x).hom.QuasiFinite) :
    letI := (f.residueFieldMap x).hom.toAlgebra
    Module.Finite (Y.residueField (f x)) (X.residueField x) := by
  let R : Type u := Y.presheaf.stalk (f x)
  let A : Type u := X.presheaf.stalk x
  let φ : R →+* A := (f.stalkMap x).hom
  let : Algebra R A := φ.toAlgebra
  let : Algebra.QuasiFinite R A := RingHom.quasiFinite_algebraMap.mp hx
  let p : Ideal R := IsLocalRing.maximalIdeal R
  let P : Ideal A := IsLocalRing.maximalIdeal A
  let : p.IsPrime := (IsLocalRing.maximalIdeal.isMaximal R).isPrime
  let : P.IsPrime := (IsLocalRing.maximalIdeal.isMaximal A).isPrime
  let : P.LiesOver p := ⟨(IsLocalRing.maximalIdeal_comap φ).symm⟩
  let : p.IsMaximal := IsLocalRing.maximalIdeal.isMaximal R
  let : P.IsMaximal := IsLocalRing.maximalIdeal.isMaximal A
  let : Algebra (Localization.AtPrime p) (Localization.AtPrime P) :=
    Localization.AtPrime.algebraOfLiesOver p P
  let : Localization.AtPrime.IsLiesOverAlgebra p P := inferInstance
  have hfinite : Module.Finite p.ResidueField P.ResidueField := inferInstance
  let eR : IsLocalRing.ResidueField R ≃+* p.ResidueField :=
    IsLocalization.AtPrime.equivQuotMaximalIdeal p (Localization.AtPrime p)
  let eA : IsLocalRing.ResidueField A ≃+* P.ResidueField :=
    IsLocalization.AtPrime.equivQuotMaximalIdeal P (Localization.AtPrime P)
  let : Algebra (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField A) :=
    (IsLocalRing.ResidueField.map φ).toAlgebra
  have hcompat : (algebraMap p.ResidueField P.ResidueField).comp eR.toRingHom =
      eA.toRingHom.comp (IsLocalRing.ResidueField.map φ) := by
    ext z
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
    show algebraMap p.ResidueField P.ResidueField
        (eR (IsLocalRing.residue R r)) =
      eA ((IsLocalRing.ResidueField.map φ) (IsLocalRing.residue R r))
    rw [IsLocalRing.ResidueField.map_residue]
    show algebraMap p.ResidueField P.ResidueField
        ((IsLocalization.AtPrime.equivQuotMaximalIdeal p (Localization.AtPrime p))
          (Ideal.Quotient.mk _ r)) =
      (IsLocalization.AtPrime.equivQuotMaximalIdeal P (Localization.AtPrime P))
        (Ideal.Quotient.mk _ (φ r))
    rw [IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk,
      IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk]
    show algebraMap p.ResidueField P.ResidueField
        (algebraMap R p.ResidueField r) = algebraMap A P.ResidueField (φ r)
    exact Ideal.ResidueField.map_algebraMap p P φ
      (IsLocalRing.maximalIdeal_comap φ).symm r
  have hdim : Module.finrank (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField A) = Module.finrank p.ResidueField P.ResidueField :=
    Algebra.finrank_eq_of_equiv_equiv eR eA hcompat
  have hpos : 0 < Module.finrank (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField A) := hdim ▸ Module.finrank_pos
  show Module.Finite (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField A)
  exact Module.finite_of_finrank_pos hpos

/-- At every point of a locally quasi-finite morphism the residue field extension is finite. -/
public theorem residueField_finite_of_locallyQuasiFinite {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyQuasiFinite f] (x : X) :
    letI := (f.residueFieldMap x).hom.toAlgebra
    Module.Finite (Y.residueField (f x)) (X.residueField x) :=
  residueField_finite_of_quasiFiniteAt f x (Scheme.Hom.quasiFiniteAt f x)

/-- A morphism surjective on stalks induces a surjective, hence finite, extension of residue
fields. -/
public theorem residueFieldMap_finite_of_surjectiveOnStalks {X Y : Scheme.{u}} (f : X ⟶ Y)
    [SurjectiveOnStalks f] (x : X) :
    letI := (f.residueFieldMap x).hom.toAlgebra
    Module.Finite (Y.residueField (f x)) (X.residueField x) := by
  let : Algebra (Y.residueField (f x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  show (f.residueFieldMap x).hom.Finite
  refine RingHom.Finite.of_surjective _ fun z ↦ ?_
  obtain ⟨a, rfl⟩ := X.residue_surjective x z
  obtain ⟨b, hb⟩ := f.stalkMap_surjective x a
  refine ⟨(Y.residue (f x)).hom b, ?_⟩
  simpa only [CommRingCat.comp_apply, hb] using
    congrArg (fun φ : Y.presheaf.stalk (f x) ⟶ X.residueField x ↦ φ.hom b)
      (Scheme.residue_residueFieldMap f x)

/-- The `k`-algebra structure on the residue field at `v` of a scheme over `Spec k`. -/
private noncomputable abbrev resAlg {V : Scheme.{u}} {k : Type u} [Field k]
    (g : V ⟶ Spec (.of k)) (v : V) : Algebra k (V.residueField v) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop ≫ V.Γevaluation v).hom.toAlgebra

/-- Along a morphism over `Spec k`, the induced residue-field map is a `k`-algebra map. -/
private theorem residueFieldMap_algebraMap {W V : Scheme.{u}} {k : Type u} [Field k]
    (a : W ⟶ V) (g : V ⟶ Spec (.of k)) (w : W) :
    letI := resAlg g (a w)
    letI := resAlg (a ≫ g) w
    ∀ z : k, (a.residueFieldMap w).hom (algebraMap k (V.residueField (a w)) z) =
      algebraMap k (W.residueField w) z := by
  intro z
  have h : (Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop ≫ V.Γevaluation (a w) ≫
      a.residueFieldMap w =
      (Scheme.ΓSpecIso (.of k)).inv ≫ (a ≫ g).appTop ≫ W.Γevaluation w := by
    rw [Scheme.Γevaluation_naturality]
    rfl
  exact congrArg (fun φ : CommRingCat.of k ⟶ W.residueField w ↦ φ.hom z) h

/-- The residue field at a point of the source is at least as transcendental over `k` as the
residue field at its image. -/
private theorem trdeg_residueField_le_of_lift {W V : Scheme.{u}} {k : Type u} [Field k]
    (a : W ⟶ V) (g : V ⟶ Spec (.of k)) (w : W) :
    letI := resAlg g (a w)
    letI := resAlg (a ≫ g) w
    Algebra.trdeg k (V.residueField (a w)) ≤ Algebra.trdeg k (W.residueField w) := by
  let := resAlg g (a w)
  let := resAlg (a ≫ g) w
  let φ : V.residueField (a w) →ₐ[k] W.residueField w :=
    { (a.residueFieldMap w).hom with
      commutes' := residueFieldMap_algebraMap a g w }
  exact trdeg_le_of_injective φ (a.residueFieldMap w).hom.injective

/-- An algebraic residue-field extension along a morphism over `k` leaves the transcendence
degree over `k` unchanged. -/
private theorem trdeg_residueField_eq_of_isAlgebraic {W V : Scheme.{u}} {k : Type u} [Field k]
    (b : W ⟶ V) (g : V ⟶ Spec (.of k)) (w : W)
    (hAlg : letI := (b.residueFieldMap w).hom.toAlgebra
      Algebra.IsAlgebraic (V.residueField (b w)) (W.residueField w)) :
    letI := resAlg g (b w)
    letI := resAlg (b ≫ g) w
    Algebra.trdeg k (V.residueField (b w)) = Algebra.trdeg k (W.residueField w) := by
  let := resAlg g (b w)
  let := resAlg (b ≫ g) w
  let : Algebra (V.residueField (b w)) (W.residueField w) :=
    (b.residueFieldMap w).hom.toAlgebra
  have : Algebra.IsAlgebraic (V.residueField (b w)) (W.residueField w) := hAlg
  have : IsScalarTower k (V.residueField (b w)) (W.residueField w) :=
    IsScalarTower.of_algebraMap_eq' (by
      ext z
      exact (residueFieldMap_algebraMap b g w z).symm)
  have : FaithfulSMul k (V.residueField (b w)) :=
    (faithfulSMul_iff_algebraMap_injective k (V.residueField (b w))).mpr
      (algebraMap k (V.residueField (b w))).injective
  have : FaithfulSMul (V.residueField (b w)) (W.residueField w) :=
    (faithfulSMul_iff_algebraMap_injective (V.residueField (b w))
      (W.residueField w)).mpr
      (algebraMap (V.residueField (b w)) (W.residueField w)).injective
  have h := trdeg_add_eq k (V.residueField (b w)) (A := (W.residueField w : Type u))
  rwa [trdeg_eq_zero (R := V.residueField (b w)) (A := W.residueField w), add_zero] at h

/-- Let `g : V ⟶ Spec k` be locally of finite type over a field and let `a, b : W ⟶ V` have the
same composite to `Spec k`. If the residue-field extension induced by `b` at `w` is algebraic
and `a w` specializes to `b w`, then the two points coincide. -/
public theorem eq_of_specialization_of_common_lift_of_isAlgebraic {W V : Scheme.{u}}
    {k : Type u} [Field k] (a b : W ⟶ V) (g : V ⟶ Spec (.of k)) [LocallyOfFiniteType g]
    (hcomp : a ≫ g = b ≫ g) (w : W)
    (hAlg : letI := (b.residueFieldMap w).hom.toAlgebra
      Algebra.IsAlgebraic (V.residueField (b w)) (W.residueField w))
    (hsp : a w ⤳ b w) : a w = b w := by
  by_contra hne
  let := resAlg g (a w)
  let := resAlg g (b w)
  let := resAlg (a ≫ g) w
  have hlt := trdeg_residueField_lt_of_specialization k V g hsp hne
  have hle := trdeg_residueField_le_of_lift a g w
  have heq := trdeg_residueField_eq_of_isAlgebraic b g w hAlg
  rw [← hcomp] at heq
  exact absurd (hle.trans heq.symm.le) (not_le_of_gt hlt)

/-- The locally quasi-finite case of
`AlgebraicGeometry.eq_of_specialization_of_common_lift_of_isAlgebraic`. -/
public theorem eq_of_specialization_of_common_lift_over_field {W V : Scheme.{u}} {k : Type u}
    [Field k] (a b : W ⟶ V) (g : V ⟶ Spec (.of k)) [LocallyOfFiniteType g]
    [LocallyQuasiFinite b] (hcomp : a ≫ g = b ≫ g) (w : W) (hsp : a w ⤳ b w) : a w = b w := by
  refine eq_of_specialization_of_common_lift_of_isAlgebraic a b g hcomp w ?_ hsp
  let : Algebra (V.residueField (b w)) (W.residueField w) :=
    (b.residueFieldMap w).hom.toAlgebra
  have : Module.Finite (V.residueField (b w)) (W.residueField w) :=
    residueField_finite_of_locallyQuasiFinite b w
  infer_instance

/-- A morphism locally of finite type whose source has no nontrivial specialization is
quasi-finite at every point. -/
public theorem forall_quasiFiniteAt_of_specialization_eq {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (h : ∀ x y : X, x ⤳ y → x = y) : ∀ x : X, quasiFiniteAt f x := by
  have : T1Space X := t1Space_iff_specializes_imp_eq.mpr fun {x y} ↦ h x y
  intro x
  have : T1Space (f.fiber (f x)) := (f.fiberι (f x)).isEmbedding.t1Space
  refine ((quasiFiniteAt_tfae f x).out 3 1).mp ?_
  exact ⟨isClosed_singleton, fun ⟨_, hne, hy⟩ ↦ hne hy.eq⟩

end AlgebraicGeometry

end
