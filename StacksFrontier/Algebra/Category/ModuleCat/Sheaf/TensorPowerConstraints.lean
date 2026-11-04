module

public import Mathlib.RingTheory.Nilpotent.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleSummandSheafify
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerCoherence
public import StacksCore.Tactic.StacksAttribute

/-!
# The commutativity constraint on the tensor powers of an invertible sheaf of modules

Let `O` be a sheaf of commutative rings on a site `(C, J)` and let `L` be an invertible sheaf of
`O`-modules. We prove that the braiding `M ⊗_O M ≅ M ⊗_O M` of an invertible sheaf of modules
with itself is the identity, so that the multiplication isomorphisms
`L^{⊗ n} ⊗_O L^{⊗ n} ≅ L^{⊗ 2n}` satisfy the commutativity constraint.

## Main results

* `Stacks.SheafOfModules.tensorSheafBraiding_self_eq_refl`: the braiding `M ⊗_O M ≅ M ⊗_O M` of
  an invertible sheaf of modules with itself is the identity.
* `Stacks.SheafOfModules.TensorPower.braidingScalar_eq_id`: the braiding scalar is the identity
  in every degree.
* `Stacks.SheafOfModules.TensorPower.commutativity_self`: every multiplication isomorphism
  `L^{⊗ n} ⊗_O L^{⊗ n} ≅ L^{⊗ 2n}` satisfies the commutativity constraint.
* `Stacks.SheafOfModules.exists_braiding_smul`: the braiding of an invertible sheaf of modules
  with itself acts on sections as multiplication by a compatible family of scalars.
* `Stacks.SheafOfModules.eq_zero_of_dualBasis_smul_tmul_self` and
  `Stacks.SheafOfModules.eq_one_of_dualBasis_smul_tmul_self`: a scalar which fixes the symmetric
  square `x k ⊗ x k` of every member of a dual basis for a pairing `ψ : M ⊗ N ⟶ R` is `1`.
* `Stacks.SheafOfModules.exists_dualBasis_cover`: a locally surjective pairing of presheaves of
  modules admits a dual basis on a covering of every object.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 0B8N](https://stacks.math.columbia.edu/tag/0B8N)
-/

@[expose] public section

open CategoryTheory Limits Opposite MonoidalCategory

open scoped TensorProduct

universe v u w

namespace Stacks.SheafOfModules

attribute [local implicit_reducible] TensorSheafification.structureSheaf

/-- If an element `δ` of a commutative ring annihilates the square of every member of a finite
family of elements which sum to `1`, then `δ = 0`. -/
theorem eq_zero_of_mul_sq_eq_zero {R : Type*} [CommRing R] {n : ℕ} (c : Fin n → R)
    (hc : ∑ i, c i = 1) {δ : R} (h : ∀ i, δ * c i ^ 2 = 0) : δ = 0 := by
  classical
  set A : Ideal R := Ideal.span (Set.range fun i ↦ c i ^ 2) with hA
  have hnil : ∀ i, IsNilpotent (Ideal.Quotient.mk A (c i)) := fun i ↦
    ⟨2, by
      rw [← map_pow]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)⟩
  have hone : (1 : R ⧸ A) = ∑ i, Ideal.Quotient.mk A (c i) := by
    rw [← map_sum, hc, map_one]
  have h2 : (1 : R ⧸ A) = 0 := by
    obtain ⟨k, hk⟩ := hone ▸ isNilpotent_sum (s := Finset.univ)
      (f := fun i ↦ Ideal.Quotient.mk A (c i)) fun i _ ↦ hnil i
    rwa [one_pow] at hk
  have h3 : (1 : R) ∈ A := Ideal.Quotient.eq_zero_iff_mem.mp (by rw [map_one, h2])
  have hle : A ≤ LinearMap.ker (LinearMap.mulLeft R δ) := by
    rw [hA, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact h i
  simpa using hle h3

/-- Let `ψ : M ⊗ N → R` be a pairing admitting a dual basis `x`, `y`, i.e. one with
`∑ ψ (x k ⊗ y k) = 1`. If a scalar `δ` annihilates the symmetric square `x k ⊗ x k` of every
member of the dual basis, then `δ = 0`. -/
theorem eq_zero_of_dualBasis_smul_tmul_self {R : Type*} [CommRing R] {M N : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (ψ : M ⊗[R] N →ₗ[R] R) {n : ℕ} (x : Fin n → M) (y : Fin n → N)
    (hsum : ∑ j, ψ (x j ⊗ₜ y j) = 1) {δ : R}
    (hz : ∀ k, δ • (x k ⊗ₜ[R] x k) = 0) : δ = 0 := by
  refine eq_zero_of_mul_sq_eq_zero (fun k ↦ ψ (x k ⊗ₜ y k)) hsum fun k ↦ ?_
  set φ : M →ₗ[R] R := ψ ∘ₗ (TensorProduct.mk R M N).flip (y k) with hφ
  set g : M ⊗[R] M →ₗ[R] R :=
    (TensorProduct.lid R R).toLinearMap ∘ₗ TensorProduct.map φ φ with hg
  have h0 : δ • g (x k ⊗ₜ[R] x k) = 0 := by rw [← map_smul, hz k, map_zero]
  have h1 : g (x k ⊗ₜ[R] x k) = ψ (x k ⊗ₜ y k) * ψ (x k ⊗ₜ y k) := by
    simp [hg, hφ, TensorProduct.lid_tmul, smul_eq_mul]
  rwa [h1, smul_eq_mul, ← pow_two] at h0

/-- A scalar fixing the symmetric square `x k ⊗ x k` of every member of a dual basis `x`, `y` for
a pairing `ψ : M ⊗ N → R` is `1`. -/
theorem eq_one_of_dualBasis_smul_tmul_self {R : Type*} [CommRing R] {M N : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (ψ : M ⊗[R] N →ₗ[R] R) {n : ℕ} (x : Fin n → M) (y : Fin n → N)
    (hsum : ∑ j, ψ (x j ⊗ₜ y j) = 1) {γ : R}
    (hz : ∀ k, γ • (x k ⊗ₜ[R] x k) = x k ⊗ₜ[R] x k) : γ = 1 :=
  sub_eq_zero.mp (eq_zero_of_dualBasis_smul_tmul_self ψ x y hsum (δ := γ - 1) fun k ↦ by
    rw [sub_smul, one_smul, hz k, sub_self])

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- A finite family of covering sieves is refined by a single covering sieve. -/
theorem exists_sieve_forall {U : C} {n : ℕ} (G : Fin n → Sieve U) (hG : ∀ k, G k ∈ J U) :
    ∃ S : Sieve U, S ∈ J U ∧ ∀ ⦃V : C⦄ (g : V ⟶ U), S g → ∀ k, G k g := by
  induction n with
  | zero => exact ⟨⊤, J.top_mem _, fun _ _ _ k ↦ k.elim0⟩
  | succ m ih =>
      obtain ⟨S, hS, hSf⟩ := ih (fun k ↦ G k.succ) fun k ↦ hG k.succ
      exact ⟨G 0 ⊓ S, J.intersection_covering (hG 0) hS,
        fun V g hg ↦ Fin.cases hg.1 (fun i ↦ hSf g hg.2 i)⟩

variable (O : Cᵒᵖ ⥤ CommRingCat.{w})
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

attribute [local instance] monoidalCategoryPresheafOfModules symmetricCategoryPresheafOfModules

section CommRingInstance

variable (hO' : Presheaf.IsSheaf J (TensorSheafification.structureRingPresheaf O))

/-- The sections of `Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO'` form a
commutative ring. -/
instance commRingTensorSheafificationStructureSheafObj (X : Cᵒᵖ) :
    CommRing ((TensorSheafification.structureSheaf O hO').obj.obj X) :=
  inferInstanceAs (CommRing (O.obj X))

end CommRingInstance

variable (hO : Presheaf.IsSheaf J (TensorSheafification.structureRingPresheaf O))

/-- Sheafifying a morphism of presheaves of modules acts on the sections in the image of the
sheafification unit by acting on their preimages. -/
theorem sheafify_map_toSheafify_app
    {A B : PresheafOfModules.{w} (TensorSheafification.structureSheaf O hO).obj} (f : A ⟶ B)
    (X : Cᵒᵖ) (a : A.obj X) :
    ((TensorSheafification.sheafify O hO).map f).val.app X
        ((TensorSheafification.toSheafify O hO A).app X a) =
      (TensorSheafification.toSheafify O hO B).app X (f.app X a) :=
  congrArg (fun φ ↦ φ.app X a)
    ((TensorSheafification.sheafifyAdjunction O hO).unit.naturality f).symm

/-- The counit of the sheafification adjunction undoes the sheafification unit of a sheaf. -/
theorem counit_toSheafify_app (P : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    (X : Cᵒᵖ) (s : P.val.obj X) :
    ((TensorSheafification.sheafifyAdjunction O hO).counit.app P).val.app X
        ((TensorSheafification.toSheafify O hO P.val).app X s) = s :=
  congrArg (fun φ ↦ φ.app X s)
    ((TensorSheafification.sheafifyAdjunction O hO).right_triangle_components P)

/-- Tensoring a sheaf of modules on the right by the structure sheaf gives it back: the right
unit constraint of the presheaf tensor product, followed by the counit of sheafification. -/
noncomputable def tensorLeftFunctorObjUnitIso
    (P : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).obj P).obj
      (SheafOfModules.unit (TensorSheafification.structureSheaf O hO)) ≅ P := by
  letI : IsIso (TensorSheafification.sheafifyAdjunction O hO).counit := by
    change IsIso (PresheafOfModules.sheafificationAdjunction
      (𝟙 (TensorSheafification.structureSheaf O hO).obj)).counit
    infer_instance
  exact (TensorSheafification.sheafify O hO).mapIso (ρ_ P.val) ≪≫
    (asIso (TensorSheafification.sheafifyAdjunction O hO).counit).app P

/-- The value of `tensorLeftFunctorObjUnitIso` on the image of a pure tensor `s ⊗ r` under the
sheafification unit is the scalar multiple `r • s`. -/
theorem tensorLeftFunctorObjUnitIso_hom_app
    (P : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO)) (X : Cᵒᵖ) (s : P.val.obj X)
    (r : (TensorSheafification.structureSheaf O hO).obj.obj X) :
    (tensorLeftFunctorObjUnitIso O hO P).hom.val.app X
        ((TensorSheafification.toSheafify O hO
          (P.val ⊗ 𝟙_ (PresheafOfModules.{w} (TensorSheafification.structureSheaf O hO).obj))).app X
            (s ⊗ₜ r)) = r • s :=
  (congrArg (fun z ↦ ((TensorSheafification.sheafifyAdjunction O hO).counit.app P).val.app X z)
      (sheafify_map_toSheafify_app O hO (ρ_ P.val).hom X (s ⊗ₜ r))).trans
    ((counit_toSheafify_app O hO P X ((ρ_ P.val).hom.app X (s ⊗ₜ r))).trans
      (ModuleCat.MonoidalCategory.rightUnitor_hom_apply s r))

/-- The braiding of an invertible sheaf of modules with itself acts on sections as
multiplication by a compatible family of sections of the structure sheaf. -/
theorem exists_braiding_smul (M : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO M] :
    ∃ c : ∀ X : Cᵒᵖ, (TensorSheafification.structureSheaf O hO).obj.obj X,
      (∀ {X Y : Cᵒᵖ} (f : X ⟶ Y),
          (TensorSheafification.structureSheaf O hO).obj.map f (c X) = c Y) ∧
        ∀ (X : Cᵒᵖ) (s : ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} (J := J)
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat
        RingCat) hO⟩).obj (M)).obj (M))).val.obj X),
          (tensorSheafBraiding O hO M M).hom.val.app X s =
            @HSMul.hSMul ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} (J := J)
              ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).obj.obj X)
              _ _ _ (c X) s := by
  let : IsInvertible O hO ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} (J := J)
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).obj (M)).obj
        (M))) :=
    isInvertible_tensorSheaf O hO M M
  set P : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO) :=
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} (J := J)
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).obj M).obj M
  set F := (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).obj P
  set κ := tensorLeftFunctorObjUnitIso O hO P
  set e := F.preimage (κ.hom ≫ (tensorSheafBraiding O hO M M).hom ≫ κ.inv) with hedef
  have key : F.map e ≫ κ.hom = κ.hom ≫ (tensorSheafBraiding O hO M M).hom := by
    refine (congrArg (fun morphism => morphism ≫ κ.hom)
      (F.map_preimage (κ.hom ≫ (tensorSheafBraiding O hO M M).hom ≫ κ.inv))).trans ?_
    exact (Category.assoc κ.hom ((tensorSheafBraiding O hO M M).hom ≫ κ.inv) κ.hom).trans
      (congrArg (fun morphism => κ.hom ≫ morphism)
        ((Category.assoc (tensorSheafBraiding O hO M M).hom κ.inv κ.hom).trans
          ((congrArg (fun morphism => (tensorSheafBraiding O hO M M).hom ≫ morphism)
            κ.inv_hom_id).trans (Category.comp_id _))))
  refine ⟨fun X ↦ e.val.app X (1 : (TensorSheafification.structureSheaf O hO).obj.obj X),
    fun {X Y} f ↦ ?_, fun X s ↦ ?_⟩
  · exact (PresheafOfModules.naturality_apply e.val f
      (1 : (TensorSheafification.structureSheaf O hO).obj.obj X)).symm.trans
        (congrArg (e.val.app Y) (PresheafOfModules.unit_map_one _ f))
  · have hRHS : (κ.hom ≫ (tensorSheafBraiding O hO M M).hom).val.app X
        ((TensorSheafification.toSheafify O hO
          (P.val ⊗ 𝟙_ (PresheafOfModules.{w} (TensorSheafification.structureSheaf O hO).obj))).app X
            (s ⊗ₜ (1 : (TensorSheafification.structureSheaf O hO).obj.obj X))) =
        (tensorSheafBraiding O hO M M).hom.val.app X s :=
      congrArg (fun z ↦ (tensorSheafBraiding O hO M M).hom.val.app X z)
        ((tensorLeftFunctorObjUnitIso_hom_app O hO P X s 1).trans
          ((P.val.obj X).isModule.one_smul s))
    refine hRHS.symm.trans ((congrArg (fun φ ↦ φ.val.app X
      ((TensorSheafification.toSheafify O hO
        (P.val ⊗ 𝟙_ (PresheafOfModules.{w} (TensorSheafification.structureSheaf O hO).obj))).app X
          (s ⊗ₜ (1 : (TensorSheafification.structureSheaf O hO).obj.obj X)))) key).symm.trans ?_)
    exact (congrArg (fun z ↦ κ.hom.val.app X z)
        (sheafify_map_toSheafify_app O hO (P.val ◁ e.val) X
          (s ⊗ₜ (1 : (TensorSheafification.structureSheaf O hO).obj.obj X)))).trans
      (tensorLeftFunctorObjUnitIso_hom_app O hO P X s _)

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- On a covering of any object, a locally surjective pairing of presheaves of modules admits a
dual basis: finitely many sections of each factor whose pairings sum to `1`. -/
theorem exists_dualBasis_cover
    {Lp Np : PresheafOfModules.{w} (TensorSheafification.structureRingPresheaf O)}
    (ψ : Lp ⊗ Np ⟶ 𝟙_ (PresheafOfModules.{w} (TensorSheafification.structureRingPresheaf O)))
    [PresheafOfModules.IsLocallySurjective J ψ] (U : C) :
    ∃ S : Sieve U, S ∈ J U ∧ ∀ ⦃V : C⦄ (g : V ⟶ U), S g →
      ∃ (n : ℕ) (x : Fin n → Lp.obj (op V)) (y : Fin n → Np.obj (op V)),
        ∑ j, ψ.app (op V) (x j ⊗ₜ y j) = (1 : O.obj (op V)) := by
  classical
  refine ⟨Presheaf.imageSieve ((PresheafOfModules.toPresheaf _).map ψ) (1 : O.obj (op U)),
    Presheaf.imageSieve_mem J ((PresheafOfModules.toPresheaf _).map ψ) _, ?_⟩
  rintro V g ⟨t, ht⟩
  obtain ⟨n, x, y, hxy⟩ := exists_fin_tmul_eq t
  refine ⟨n, x, y, ?_⟩
  exact (map_sum _ _ _).symm.trans ((congrArg (fun z ↦ ψ.app (op V) z) hxy).trans
    (ht.trans (PresheafOfModules.unit_map_one _ _)))

/-- The braiding of an invertible sheaf of modules with itself is the identity. -/
theorem tensorSheafBraiding_self_eq_refl
    (M : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO)) [IsInvertible O hO M] :
    tensorSheafBraiding O hO M M = Iso.refl _ := by
  obtain ⟨Mp, hMp, rfl⟩ :
      ∃ (Mp : PresheafOfModules.{w} (TensorSheafification.structureSheaf O hO).obj)
        (hMp : Presheaf.IsSheaf J Mp.presheaf),
        M = (⟨Mp, hMp⟩ : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO)) :=
    ⟨M.val, M.isSheaf, rfl⟩
  obtain ⟨Np, ψ, hsurj, hinj⟩ := exists_locallyBijective_pairing (hO := hO) hMp inferInstance
  have hli : PresheafOfModules.IsLocallyInjective J
      (TensorSheafification.toSheafify O hO (Mp ⊗ Mp)) :=
    inferInstanceAs (Presheaf.IsLocallyInjective J
      (CategoryTheory.toSheafify J (Mp ⊗ Mp).presheaf))
  obtain ⟨c, hcnat, hc⟩ :=
    exists_braiding_smul O hO
      (⟨Mp, hMp⟩ : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
  have hfix : ∀ (X : Cᵒᵖ) (a : Mp.obj X),
      (TensorSheafification.toSheafify O hO (Mp ⊗ Mp)).app X
          (c X • (a ⊗ₜ[(TensorSheafification.structureSheaf O hO).obj.obj X] a)) =
        (TensorSheafification.toSheafify O hO (Mp ⊗ Mp)).app X
          (a ⊗ₜ[(TensorSheafification.structureSheaf O hO).obj.obj X] a) := by
    intro X a
    refine (((TensorSheafification.toSheafify O hO (Mp ⊗ Mp)).app X).hom.map_smul (c X)
      (a ⊗ₜ[(TensorSheafification.structureSheaf O hO).obj.obj X] a)).trans ?_
    exact (hc X ((TensorSheafification.toSheafify O hO (Mp ⊗ Mp)).app X (a ⊗ₜ a))).symm.trans
      (sheafify_map_toSheafify_app O hO (β_ Mp Mp).hom X (a ⊗ₜ a))
  have hone : ∀ X : Cᵒᵖ, c X = 1 := by
    have hdown : ∀ {Y Z : C} (g : Z ⟶ Y), c (op Y) = 1 → c (op Z) = 1 := fun {Y Z} g h ↦ by
      rw [← hcnat g.op, h]
      exact PresheafOfModules.unit_map_one _ g.op
    set T : (U : C) → Sieve U := fun U ↦
      { arrows := fun V _ ↦ c (op V) = 1
        downward_closed := fun hf g ↦ hdown g hf }
    have hT : ∀ U : C, T U ∈ J U := by
      intro U
      obtain ⟨S₁, hS₁, hS₁spec⟩ := exists_dualBasis_cover (J := J) O ψ U
      refine J.transitive hS₁ (T U) fun {V} {g} hg ↦ ?_
      obtain ⟨n, x, y, hxy⟩ := hS₁spec g hg
      obtain ⟨S₂, hS₂, hS₂spec⟩ := exists_sieve_forall
        (fun k ↦ Presheaf.equalizerSieve (F := (Mp ⊗ Mp).presheaf) (X := op V)
          (c (op V) • (x k ⊗ₜ[(TensorSheafification.structureSheaf O hO).obj.obj (op V)] x k))
          (x k ⊗ₜ[(TensorSheafification.structureSheaf O hO).obj.obj (op V)] x k))
        (fun k ↦ Presheaf.equalizerSieve_mem J
          ((PresheafOfModules.toPresheaf _).map (TensorSheafification.toSheafify O hO (Mp ⊗ Mp)))
          _ _ (hfix (op V) (x k)))
      refine J.superset_covering (fun W g' hg' ↦ ?_) hS₂
      show c (op W) = 1
      refine eq_one_of_dualBasis_smul_tmul_self (ψ.app (op W)).hom
        (fun k ↦ Mp.map g'.op (x k)) (fun k ↦ Np.map g'.op (y k)) ?_ fun k ↦ ?_
      · have h3 : ∀ k, ψ.app (op W) (Mp.map g'.op (x k) ⊗ₜ Np.map g'.op (y k))
            = (𝟙_ (PresheafOfModules.{w} (TensorSheafification.structureSheaf O hO).obj)).map g'.op
                (ψ.app (op V) (x k ⊗ₜ y k)) := fun k ↦
          PresheafOfModules.naturality_apply ψ g'.op (x k ⊗ₜ y k)
        refine (Finset.sum_congr rfl fun k _ ↦ h3 k).trans ?_
        refine ((map_sum _ _ _).symm.trans (congrArg _ hxy)).trans ?_
        exact PresheafOfModules.unit_map_one _ g'.op
      · have h2 : (Mp ⊗ Mp).map g'.op
              (c (op V) • (x k ⊗ₜ[(TensorSheafification.structureSheaf O hO).obj.obj (op V)] x k)) =
            (Mp ⊗ Mp).map g'.op
              (x k ⊗ₜ[(TensorSheafification.structureSheaf O hO).obj.obj (op V)] x k) :=
          hS₂spec g' hg' k
        exact (congrArg (fun z ↦ z • (Mp ⊗ Mp).map g'.op
                (x k ⊗ₜ[(TensorSheafification.structureSheaf O hO).obj.obj (op V)] x k))
              (hcnat g'.op)).symm.trans
          (((Mp ⊗ Mp).map_smul g'.op (c (op V))
            (x k ⊗ₜ[(TensorSheafification.structureSheaf O hO).obj.obj (op V)] x k)).symm.trans h2)
    intro X
    refine (SheafOfModules.unit
      (TensorSheafification.structureSheaf O hO)).isSheaf.isSeparated X.unop (T X.unop) (hT X.unop)
        (c X) (1 : (TensorSheafification.structureSheaf O hO).obj.obj (op X.unop)) fun Y f hf ↦ ?_
    exact (hcnat f.op).trans (hf.trans (PresheafOfModules.unit_map_one _ f.op).symm)
  refine Iso.ext (SheafOfModules.Hom.ext (PresheafOfModules.hom_ext fun X ↦
    ModuleCat.hom_ext (LinearMap.ext fun s ↦ ?_)))
  rw [hc X s, hone X]
  exact (ModuleCat.isModule _).one_smul s

namespace TensorPower

variable (L : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO)) [IsInvertible O hO L]

/-- The braiding of a tensor power of an invertible sheaf of modules with itself is the
identity. -/
theorem tensorSheafBraiding_tensorPower_self_eq_refl (n : ℤ) :
    tensorSheafBraiding O hO (tensorPower O hO L n) (tensorPower O hO L n) = Iso.refl _ :=
  tensorSheafBraiding_self_eq_refl O hO (tensorPower O hO L n)

/-- The braiding scalar of the tensor powers of an invertible sheaf of modules is the identity,
in every degree. -/
@[stacks 01CU "commutativity constraint"]
theorem braidingScalar_eq_id (n : ℤ) : braidingScalar O hO L n = 𝟙 _ :=
  (tensorSheafBraiding_self_eq_refl_iff O hO L n).mp
    (tensorSheafBraiding_tensorPower_self_eq_refl O hO L n)

/-- Every isomorphism `μ : L^{⊗ n} ⊗_O L^{⊗ n} ≅ L^{⊗ (n + n)}` satisfies the commutativity
constraint: precomposing it with the braiding does not change it. -/
theorem commutativity_self (n : ℤ)
    (μ : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} (J := J)
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).obj
        ((tensorPower O hO L n))).obj ((tensorPower O hO L n))) ≅
      tensorPower O hO L (n + n)) :
    μ = tensorSheafBraiding O hO (tensorPower O hO L n) (tensorPower O hO L n) ≪≫ μ ≪≫
      tensorPowerReindex O hO L (Int.add_comm n n) := by
  rw [tensorPowerReindex_rfl, tensorSheafBraiding_tensorPower_self_eq_refl]
  exact Iso.ext ((Category.id_comp (μ.hom ≫ 𝟙 _)).trans (Category.comp_id μ.hom)).symm

end TensorPower

end Stacks.SheafOfModules

end
