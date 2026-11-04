module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ConstantSmoothCurve
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.RestrictionComposition

/-!
# Injectivity of the comparison with an extension of algebraically closed fields (Tag 0A58)

Let `X` be a scheme over an algebraically closed field `k`, `k'/k` a field extension and `F` an
abelian sheaf on `X_étale`. Write `k'` as the filtered union of its finitely generated
`k`-subalgebras `A`. By Tag 03Q6, `H^q(X_{k'}, F) = colim_A H^q(X_A, F)`; so a class `x` of
`H^q(X, F)` which dies on `X_{k'}` already dies on some `X_A`. Each `A` has a `k`-point
(Hilbert's Nullstellensatz, `k` being algebraically closed), so `X_A ⟶ X` has a section, and the
restriction of `x` to `X_A` determines `x`. Hence `H^q(X, F) ⟶ H^q(X_{k'}, F)` is injective.

Together with the equality of the (finite) orders of the two groups, which the computations of
Tags 03RQ and 03RR give, this is the base change assertion (6) of Tag 03SC for `Z/ℓ` on a smooth
curve (the argument behind Tag 0A58).

The colimit statement of Tag 03Q6 enters through its elementwise consequence, the hypothesis
`h03Q6` of `injective_scalarExtension_of_fg`.

## Main results

* `Stacks.EtaleCohomology.injective_etaleCohomologyRestrictionMap_of_retract`.
* `Stacks.EtaleCohomology.injective_scalarExtension_of_fg`.
* `Stacks.EtaleCohomology.bijective_of_injective_of_natCard_eq`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-- **A class determined on a retract.** If every class `x` of `H^q(X, F)` killed by restriction
along `g` is also killed by restriction along some `a : Z ⟶ X` admitting a section, then
restriction along `g` is injective. -/
theorem injective_etaleCohomologyRestrictionMap_of_retract {X Y : Scheme.{u}} (g : Y ⟶ X)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (h : ∀ x : Sheaf.H.{u + 1} F q, etaleCohomologyRestrictionMap.{u, u + 1, u + 1} g F q x = 0 →
      ∃ (Z : Scheme.{u}) (a : Z ⟶ X) (s : X ⟶ Z), s ≫ a = 𝟙 X ∧
        etaleCohomologyRestrictionMap.{u, u + 1, u + 1} a F q x = 0) :
    Function.Injective (etaleCohomologyRestrictionMap.{u, u + 1, u + 1} g F q) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨Z, a, s, hsa, hax⟩ := h x hx
  have hc := etaleCohomologyRestrictionMap_comp_eq_comp_mk₀.{u, u + 1, u + 1} a s (𝟙 X) hsa.symm
    F q x
  rw [hax, map_zero] at hc
  set e := etaleAbelianInverseImageCompIso'.{u, u + 1} s a (𝟙 X) hsa.symm
  have hinv : e.hom.app F ≫ e.inv.app F = 𝟙 _ := by
    rw [← NatTrans.comp_app, Iso.hom_inv_id, NatTrans.id_app]
  have h1 : etaleCohomologyRestrictionMap.{u, u + 1, u + 1} (𝟙 X) F q x = 0 := by
    have := congrArg (fun z => z.comp (Ext.mk₀ (e.inv.app F)) (add_zero q)) hc
    simp only [Ext.zero_comp] at this
    rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, hinv, Ext.comp_mk₀_id] at this
    exact this.symm
  have := universalHomeomorphism_of_isIso (𝟙 X)
  exact (etaleCohomologyRestrictionMap_bijective_of_universalHomeomorphism.{u, u + 1, u + 1}
    (𝟙 X) F q).1 (h1.trans (map_zero _).symm)

variable {k : Type u} [Field k]

/-- The base change of `X` along `Spec A ⟶ Spec k` has a section when `A` has a `k`-point. -/
theorem exists_section_pullback_fst {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (A : Type u)
    [CommRing A] [Algebra k A] (φ : A →ₐ[k] k) :
    ∃ s : X ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap k A))),
      s ≫ pullback.fst _ _ = 𝟙 X := by
  have hφ : CommRingCat.ofHom (algebraMap k A) ≫ CommRingCat.ofHom (φ : A →+* k) = 𝟙 _ := by
    ext c
    simp
  refine ⟨pullback.lift (𝟙 X) (f ≫ Spec.map (CommRingCat.ofHom (φ : A →+* k))) ?_,
    pullback.lift_fst _ _ _⟩
  rw [Category.id_comp, Category.assoc, ← Spec.map_comp, hφ, Spec.map_id, Category.comp_id]

/-- **Injectivity of the comparison with a field extension, from Tag 03Q6.** Let `k` be
algebraically closed, `X` a scheme over `k`, `k'/k` a field extension and `F` an abelian sheaf
on `X_étale`. Suppose (the elementwise content of Tag 03Q6 for the system of finitely generated
`k`-subalgebras of `k'`) that a class of `H^q(X, F)` vanishing on `X_{k'}` vanishes on `X_A`
for some finitely generated `k`-subalgebra `A ⊆ k'`. Then `H^q(X, F) ⟶ H^q(X_{k'}, F)` is
injective. -/
theorem injective_scalarExtension_of_fg [IsAlgClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (k' : Type u) [Field k'] [Algebra k k']
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (h03Q6 : ∀ x : Sheaf.H.{u + 1} F q,
      etaleCohomologyRestrictionMap.{u, u + 1, u + 1} (scalarExtensionFst k k' f) F q x = 0 →
      ∃ A : Subalgebra k k', A.FG ∧ etaleCohomologyRestrictionMap.{u, u + 1, u + 1}
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k A)))) F q x = 0) :
    Function.Injective
      (etaleCohomologyRestrictionMap.{u, u + 1, u + 1} (scalarExtensionFst k k' f) F q) := by
  refine injective_etaleCohomologyRestrictionMap_of_retract _ F q fun x hx => ?_
  obtain ⟨A, hA, hxA⟩ := h03Q6 x hx
  have : Algebra.FiniteType k A := Subalgebra.fg_iff_finiteType A |>.mp hA
  -- a `k`-point of `A` (Hilbert's Nullstellensatz)
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  let : m.IsMaximal := hm
  let : Field (A ⧸ m) := Ideal.Quotient.field m
  let : Algebra.FiniteType k (A ⧸ m) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k m) Ideal.Quotient.mk_surjective
  let : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := k) (B := A)
  let : Module.Finite k (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (A ⧸ m)
  have hbij : Function.Bijective (algebraMap k (A ⧸ m)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := A ⧸ m)
  let φ : A →ₐ[k] k := (AlgEquiv.ofBijective (Algebra.ofId k (A ⧸ m)) hbij).symm.toAlgHom.comp
    (Ideal.Quotient.mkₐ k m)
  obtain ⟨s, hs⟩ := exists_section_pullback_fst f A φ
  exact ⟨_, _, s, hs, hxA⟩

end Stacks.EtaleCohomology

end
