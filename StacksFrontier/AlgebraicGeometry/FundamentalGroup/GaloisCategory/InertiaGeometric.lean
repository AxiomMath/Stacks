module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCategory.GaloisFixedPoints
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Inertia acts trivially on constants and on points of finite étale schemes over the constants

Let `k` be a finite field, `K` a field over `k`, `A` a domain with fraction field `K`, `L` an
algebraic extension of `K` and `P` a maximal ideal of the integral closure of `A` in `L`. An
element `σ` of the inertia group of `P` fixes every element of `L` integral over `k`
(`AlgebraicGeometry.inertia_apply_eq_of_isIntegral`): `σ z - z` lies in a finite field, so is a
root of `T ^ Q - T`, a unit of the integral closure when nonzero, yet it lies in `P`. An element of
`Gal(L/K)` fixing the elements of `L` integral over `k` fixes every `L`-point of a finite étale
`k`-scheme (`AlgebraicGeometry.spec_comp_eq_of_forall_isIntegral`): such a scheme is affine with
coordinate ring integral over `k`. So the inertia at a place of a curve over `k` lies in the
geometric fundamental group, as used in [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **Inertia fixes the constants**: an element of the inertia group of a maximal ideal `P` of
the integral closure of `A` in `L` fixes every element of `L` integral over a finite field. -/
theorem inertia_apply_eq_of_isIntegral {k K L A : Type*} [Field k] [Finite k] [Field K]
    [Field L] [CommRing A] [IsDomain A] [Algebra A K] [IsFractionRing A K] [Algebra K L]
    [Algebra A L] [IsScalarTower A K L] [Algebra.IsAlgebraic K L] [Algebra k K] [Algebra k L]
    [IsScalarTower k K L] (P : Ideal (integralClosure A L)) [P.IsMaximal] (σ : Gal(L/K))
    (hσ : letI := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
      σ ∈ P.inertia Gal(L/K)) {z : L} (hz : _root_.IsIntegral k z) : σ z = z := by
  classical
  let := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
  -- `z` and `σ z` lie in a finite field `F`
  have hσz : _root_.IsIntegral k (σ z) := hz.map ((σ.restrictScalars k).toAlgHom)
  let F := IntermediateField.adjoin k ({z, σ z} : Set L)
  have : FiniteDimensional k F := IntermediateField.finiteDimensional_adjoin fun x hx => by
    rcases hx with rfl | rfl <;> assumption
  have : Finite F := Module.finite_of_finite k
  let : Fintype F := Fintype.ofFinite F
  have hzF : z ∈ F := IntermediateField.subset_adjoin k _ (Set.mem_insert _ _)
  have hσzF : σ z ∈ F := IntermediateField.subset_adjoin k _ (Set.mem_insert_of_mem _ rfl)
  set Q := Fintype.card F
  have hQ1 : 1 < Q := Fintype.one_lt_card
  have hpow : ∀ y ∈ F, y ^ Q = y := fun y hy =>
    congrArg Subtype.val (FiniteField.pow_card (⟨y, hy⟩ : F))
  -- `z` is integral over `A`
  have hzA : _root_.IsIntegral A z :=
    ⟨Polynomial.X ^ Q - Polynomial.X, Polynomial.monic_X_pow_sub (by
      rw [Polynomial.degree_X]
      exact_mod_cast hQ1), by simp [hpow z hzF]⟩
  let z' : integralClosure A L := ⟨z, hzA⟩
  let v : integralClosure A L := σ • z' - z'
  have hv : (v : L) = σ z - z := by
    show algebraMap (integralClosure A L) L
      (galRestrict A K L (integralClosure A L) σ z' - z') = _
    rw [map_sub, algebraMap_galRestrict_apply]
    rfl
  have hvP : v ∈ P := Ideal.mem_inertia.1 hσ z'
  have hvQ : v ^ Q = v := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, hv]
    exact hpow _ (F.sub_mem hσzF hzF)
  by_contra hne
  have hv0 : v ≠ 0 := fun h0 => hne (sub_eq_zero.1 (hv ▸ congrArg Subtype.val h0))
  have h1 : v ^ (Q - 1) = 1 := by
    apply mul_left_cancel₀ hv0
    rw [← pow_succ', Nat.sub_add_cancel hQ1.le, hvQ, mul_one]
  have hunit : IsUnit v := by
    refine isUnit_iff_exists_inv.2 ⟨v ^ (Q - 2), ?_⟩
    rw [← pow_succ', show Q - 2 + 1 = Q - 1 by omega, h1]
  exact Ideal.IsMaximal.ne_top ‹_› (Ideal.eq_top_of_isUnit_mem P hvP hunit)

/-- **An element fixing the elements integral over `k` fixes every `L`-point of a finite étale
`k`-scheme.** -/
theorem spec_comp_eq_of_forall_isIntegral {k K L : Type u} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra K L] [Algebra k L] [IsScalarTower k K L] (σ : Gal(L/K))
    (hσ : ∀ z : L, _root_.IsIntegral k z → σ z = z) (Y : FiniteEtaleOver (Spec (.of k)))
    (g : Spec (.of L) ⟶ Y.left)
    (hg : g ≫ Y.hom = Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k K))) :
    Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫ g = g := by
  have : IsFinite Y.hom := Y.prop.1
  have : IsAffine ((Functor.fromPUnit (Spec (.of k))).obj Y.right) :=
    inferInstanceAs (IsAffine (Spec (.of k)))
  have : IsAffine Y.left := isAffine_of_isAffineHom Y.hom
  have hfin : (Y.hom.appTop).hom.Finite := by
    have heq : Spec.map Y.hom.appTop = Y.left.isoSpec.inv ≫ Y.hom ≫
        ((Functor.fromPUnit (Spec (.of k))).obj Y.right).isoSpec.hom := by
      rw [← Scheme.isoSpec_hom_naturality, Iso.inv_hom_id_assoc]
    rw [← IsFinite.SpecMap_iff, heq]
    infer_instance
  let ψ : CommRingCat.of k ⟶ Γ(Y.left, ⊤) := (Scheme.ΓSpecIso (.of k)).inv ≫ Y.hom.appTop
  have hψ : ψ.hom.Finite := by
    show (Y.hom.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom).Finite
    exact hfin.comp (RingHom.Finite.of_surjective _
      (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv.surjective)
  -- the composite `k → Γ(Y) → Γ(Spec L) ≅ L` is the structure map
  let θ : Γ(Y.left, ⊤) ⟶ CommRingCat.of L := g.appTop ≫ (Scheme.ΓSpecIso (.of L)).hom
  have h1 : Y.hom.appTop ≫ g.appTop = (Spec.map (CommRingCat.ofHom (algebraMap k K) ≫
      CommRingCat.ofHom (algebraMap K L))).appTop := by
    rw [Spec.map_comp, ← hg, Scheme.Hom.comp_appTop]
  have hθ : ψ ≫ θ = CommRingCat.ofHom (algebraMap k L) := by
    show (Scheme.ΓSpecIso (.of k)).inv ≫ Y.hom.appTop ≫ g.appTop ≫
      (Scheme.ΓSpecIso (.of L)).hom = _
    rw [← Category.assoc Y.hom.appTop g.appTop, h1, Scheme.ΓSpecIso_naturality,
      Iso.inv_hom_id_assoc]
    ext c
    exact (IsScalarTower.algebraMap_apply k K L c).symm
  apply ext_of_isAffine
  rw [Scheme.Hom.comp_appTop]
  ext b
  apply (Scheme.ΓSpecIso (.of L)).commRingCatIsoToRingEquiv.injective
  show ((Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom)).appTop ≫
    (Scheme.ΓSpecIso (.of L)).hom).hom (g.appTop.hom b) = θ.hom b
  rw [Scheme.ΓSpecIso_naturality]
  show σ (θ.hom b) = θ.hom b
  apply hσ
  obtain ⟨q, hq, hq0⟩ := hψ.to_isIntegral b
  refine ⟨q, hq, ?_⟩
  have h := congrArg θ.hom hq0
  rw [map_zero, Polynomial.hom_eval₂] at h
  rw [← h]
  congr 1
  exact (congrArg CommRingCat.Hom.hom hθ).symm

end AlgebraicGeometry

end
