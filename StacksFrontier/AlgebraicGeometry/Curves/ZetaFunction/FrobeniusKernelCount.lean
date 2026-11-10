module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.JacobianFrobenius
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.PicardFunctorRepresentable
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.IsogenyKernelCount
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.PicardDegreeZeroDivisible
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SmoothSupportSpecialization
public import StacksFrontier.AlgebraicGeometry.Picard.TorsionCharpoly

/-!
# Kernels of polynomials in a twisted Frobenius on `Pic⁰` of a curve

Let `X` be a smooth proper curve of genus `g` over an algebraically closed field `k` of
characteristic `p`, and `Ψ : X ⟶ X` lying over the `n`-fold Frobenius of `Spec k` (`n ≥ 1`).
Through the Frobenius endomorphism `F` of the Jacobian `J` (which is `Ψ^*` on `J(k) = Pic⁰(X)`,
kills tangent vectors and is a homomorphism), for every `R ∈ ℤ[X]` with `p ∤ R(0)` the
endomorphism `R(F)` of `J` has derivative `R(0)` at the identity, so is étale, and its kernel
on `J(k)` has `deg R(F)` elements. The degree is a norm form `R ↦ N(R mod χ)` for a monic
`χ ∈ ℚ[X]` of degree `2 dim J = 2g`. Also `Pic⁰(X)[ℓ^N] ≅ (ℤ/ℓ^N)^{2g}` for `ℓ ≠ p`.

## Main results

* `Stacks.Zeta.exists_normForm_natCard_ker_twistedFrobenius`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Stacks.Frobenius Polynomial
open MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace Stacks.Zeta

/-- A polynomial in an endomorphism `α` of a commutative group object, read on points: if
`x ↦ x ≫ α` is carried to `u` by an additive identification `e` of the points, then
`x ↦ x ≫ R(α)` is carried to `R(u)`. -/
theorem endPolyEval_comp_eq_aeval {C : Type*} [Category C] [CartesianMonoidalCategory C]
    [BraidedCategory C] {G : C} [GrpObj G] [IsCommMonObj G] (α : G ⟶ G) [IsMonHom α] {Y : C}
    {P : Type*} [AddCommGroup P] (e : Additive (Y ⟶ G) ≃+ P) (u : P →+ P)
    (hu : ∀ x : Y ⟶ G, e (Additive.ofMul (x ≫ α)) = u (e (Additive.ofMul x))) (R : ℤ[X])
    (x : Y ⟶ G) :
    e (Additive.ofMul (x ≫ Stacks.Groupoids.endPolyEval α R)) =
      aeval (Stacks.Picard.asEnd u) R (e (Additive.ofMul x)) := by
  induction R using Polynomial.induction_on generalizing x with
  | C c =>
    rw [Stacks.Groupoids.endPolyEval_C, GrpObj.comp_zpow, Category.comp_id, aeval_C,
      algebraMap_int_eq, eq_intCast, AddMonoid.End.intCast_apply, ← map_zsmul]
    rfl
  | add R S hR hS =>
    rw [Stacks.Groupoids.endPolyEval_add, MonObj.comp_mul, map_add,
      show Additive.ofMul (x ≫ Stacks.Groupoids.endPolyEval α R *
          x ≫ Stacks.Groupoids.endPolyEval α S) =
        Additive.ofMul (x ≫ Stacks.Groupoids.endPolyEval α R) +
          Additive.ofMul (x ≫ Stacks.Groupoids.endPolyEval α S) from rfl, map_add, hR, hS]
    rfl
  | monomial m c ih =>
    have hpow : Polynomial.C c * Polynomial.X ^ (m + 1) =
        (Polynomial.C c * Polynomial.X ^ m) * Polynomial.X := by ring
    have hR : aeval (Stacks.Picard.asEnd u) (Polynomial.C c * Polynomial.X ^ m * Polynomial.X) =
        aeval (Stacks.Picard.asEnd u) (Polynomial.C c * Polynomial.X ^ m) *
          Stacks.Picard.asEnd u := by
      rw [map_mul, aeval_X]
    rw [hpow, Stacks.Groupoids.endPolyEval_mul, Stacks.Groupoids.endPolyEval_X,
      ← Category.assoc, ih, hu, hR]
    rfl

variable {k : Type u} [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p]
  {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [IsCurve k g] [Smooth g] [IsProper g]
  (hdim : topologicalKrullDim X ≤ 1) (n : ℕ) (hn : 0 < n) (Ψ : X ⟶ X)
  (hΨ : Ψ ≫ g = g ≫ Spec.map (CommRingCat.ofHom (iterateFrobenius k p n)))

include hn hΨ in
/-- **The Frobenius of the Jacobian of a curve with a twisted Frobenius `Ψ`**: an abelian variety
`J` of dimension `genus g` with `J(k) ≅ Pic⁰(X)` and a homomorphism `F : J ⟶ J` which is `Ψ^*`
on `J(k)` and kills tangent vectors at the identity. -/
theorem exists_jacobianFrobenius_data :
    ∃ (A : Over (Spec (.of k))) (_ : GrpObj A) (_ : IsAbelianVariety k A)
      (E : Additive (𝟙_ (Over (Spec (.of k))) ⟶ A) ≃+ picardDegreeZero k g hdim)
      (F : A ⟶ A) (_ : IsMonHom F),
      Stacks.Groupoids.abelianVarietyDimension A = genus g ∧
      (∀ x : 𝟙_ (Over (Spec (.of k))) ⟶ A,
        (Stacks.GluePicard.picardModelAddEquiv X.toRingedSpace).symm
            (E (Additive.ofMul (x ≫ F))).1 =
          Stacks.Picard.schemePullbackClass Ψ
            ((Stacks.GluePicard.picardModelAddEquiv X.toRingedSpace).symm
              (E (Additive.ofMul x)).1)) ∧
      ∀ (s : Spec (.of k)) (v : DottedTangentArrow A.hom ((η[A]).left s)),
        (Over.homMk v.val v.property.2 :
          Over.mk (dualNumberBasePoint A.hom ((η[A]).left s)) ⟶ A) ≫ F = 1 := by
  let S₀ : Set Scheme.{u} := {X, Spec (.of k)}
  have : Small.{u} S₀ := by dsimp [S₀]; infer_instance
  obtain ⟨B, hB⟩ := BigFppfSite.exists_containing S₀
  have hX : B.Contains X := hB X (by simp [S₀])
  have hk : B.Contains (Spec (.of k)) := hB _ (by simp [S₀])
  let f : B.obj hX ⟶ B.obj hk := ObjectProperty.homMk g
  have : IsCurve k (B.inclusion.map f) := ‹IsCurve k g›
  have : Smooth (B.inclusion.map f) := ‹Smooth g›
  have : IsProper (B.inclusion.map f) := ‹IsProper g›
  have : IrreducibleSpace X := inferInstance
  have : GeometricallyIrreducible (B.inclusion.map f) :=
    geometricallyIrreducible_of_irreducibleSpace_of_isSepClosed k X g
  have hproj : IsProjective (B.inclusion.map f) :=
    (isProjectiveVariety_iff_isProjective k g).1
      ((isProjectiveVariety_iff_isProjectiveMorphism k g).2
        (isProjectiveMorphism_of_isProper_of_isCurve k g))
  have : IsProjectiveVariety k (B.inclusion.map f) :=
    (isProjectiveVariety_iff_isProjective k g).2 hproj
  have : Nonempty X := inferInstance
  obtain ⟨σ, hσ⟩ := Stacks.RigidifiedPicard.exists_section_of_smooth_of_isSepClosed k g
  have := Stacks.RigidifiedPicard.isRepresentable_picardFunctor_of_isSepClosed k B hX hk f
    (isProjectiveMorphism_of_isProper_of_isCurve k g)
  have := Stacks.PicardFunctor.isAbelianVariety_jacobian B hX hk f σ hσ
  have hS : IsInCharacteristic (Spec (.of k)) p :=
    isInCharacteristic_spec k p (CharP.cast_eq_zero k p)
  have hΨ' : Ψ ≫ B.inclusion.map f =
      B.inclusion.map f ≫ absoluteFrobeniusPow (Spec (.of k)) p hS n := by
    rw [← specMap_eq_absoluteFrobeniusPow (iterateFrobenius k p n) p n hS
      (fun a => iterateFrobenius_def p n a)]
    exact hΨ
  set A := (Stacks.PicardFunctor.jacobianGrp B hX hk f σ hσ).X
  have : SmoothOfRelativeDimension (genus (B.inclusion.map f)) A.hom :=
    Stacks.PicardFunctor.smoothOfRelativeDimension_picardSchemeDegreeComponent B hX hk f σ hσ 0
  have : Nonempty A.left := ⟨(η[A]).left (IsLocalRing.closedPoint k)⟩
  have hdimA : Stacks.Groupoids.abelianVarietyDimension A = genus g := by
    have h1 := topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field
      (genus (B.inclusion.map f)) A.hom
    have h2 := Stacks.Groupoids.topologicalKrullDim_eq_abelianVarietyDimension A
    rw [h1] at h2
    exact_mod_cast h2.symm
  exact ⟨A, inferInstance, inferInstance,
    Stacks.PicardFunctor.jacobianPointsAddEquiv B hX hk f σ hσ hdim,
    Stacks.PicardFunctor.jacobianFrobenius B hX hk f p hS n Ψ hΨ' σ hσ, inferInstance, hdimA,
    Stacks.PicardFunctor.jacobianPointsAddEquiv_comp_jacobianFrobenius B hX hk f p hS n Ψ hΨ'
      σ hσ hdim,
    Stacks.PicardFunctor.tangent_comp_jacobianFrobenius B hX hk f p hS n Ψ hΨ' σ hσ hn⟩

/-- `Pic⁰(X)` in the model `Stacks.Picard.ofScheme` is `picardDegreeZero` in the model
`schemePicard`. -/
def picardDegreeZeroModelAddEquiv :
    (Stacks.Picard.picardDegree g hdim).ker ≃+ picardDegreeZero k g hdim :=
  (Stacks.GluePicard.picardModelAddEquiv X.toRingedSpace).addSubgroupMap _ |>.trans
    (AddEquiv.addSubgroupCongr (by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact (Stacks.Picard.picardDegree_picardModelAddEquiv g hdim z).trans hz
      · intro hy
        refine ⟨(Stacks.GluePicard.picardModelAddEquiv X.toRingedSpace).symm y, ?_, by simp⟩
        change Stacks.Picard.picardDegree g hdim _ = 0
        rw [← Stacks.Picard.picardDegree_picardModelAddEquiv g hdim, AddEquiv.apply_symm_apply]
        exact hy))

omit [IsAlgClosed k] [Smooth g] in
/-- In `schemePicard X`, `picardDegreeZeroModelAddEquiv` sends `y` to its image under
`Stacks.GluePicard.picardModelAddEquiv`. -/
theorem coe_picardDegreeZeroModelAddEquiv (y : (Stacks.Picard.picardDegree g hdim).ker) :
    ((picardDegreeZeroModelAddEquiv g hdim y : picardDegreeZero k g hdim) : schemePicard X) =
      Stacks.GluePicard.picardModelAddEquiv X.toRingedSpace y := rfl

omit [IsAlgClosed k] [Smooth g] in
/-- In `Stacks.Picard.ofScheme X`, the inverse of `picardDegreeZeroModelAddEquiv` sends `z` to
the image of `z` under the inverse of `Stacks.GluePicard.picardModelAddEquiv`. -/
theorem coe_picardDegreeZeroModelAddEquiv_symm (z : picardDegreeZero k g hdim) :
    (((picardDegreeZeroModelAddEquiv g hdim).symm z : (Stacks.Picard.picardDegree g hdim).ker) :
        Stacks.Picard.ofScheme X) =
      (Stacks.GluePicard.picardModelAddEquiv X.toRingedSpace).symm z.1 := by
  rw [AddEquiv.eq_symm_apply, ← coe_picardDegreeZeroModelAddEquiv, AddEquiv.apply_symm_apply]

include hn hΨ in
/-- **Kernel counts for polynomials in a twisted Frobenius on `Pic⁰`** (the input of
`Stacks.Picard.charpoly_levelMatrix_eq`). Let `u` be `Ψ^*` on `Pic⁰(X)`. There is a monic
`χ ∈ ℚ[X]` of degree `2g` with `#Ker R(u) = N(R mod χ)` for every `R ∈ ℤ[X]` with `p ∤ R(0)`,
and `Pic⁰(X)[ℓ^N] ≅ (ℤ/ℓ^N)^{2g}` for every prime `ℓ ≠ p`. -/
theorem exists_normForm_natCard_ker_twistedFrobenius
    (u : (Stacks.Picard.picardDegree g hdim).ker →+ (Stacks.Picard.picardDegree g hdim).ker)
    (hu : ∀ c, (u c : Stacks.Picard.ofScheme X) = Stacks.Picard.schemePullbackClass Ψ c) :
    ∃ χ : ℚ[X], χ.Monic ∧ χ.natDegree = 2 * genus g ∧
      0 ≤ Stacks.Polynomial.normForm χ Polynomial.X ∧
      (∀ R : ℤ[X], ¬ (p : ℤ) ∣ R.coeff 0 →
        (Nat.card (aeval (Stacks.Picard.asEnd u) R).ker : ℚ) = Stacks.Polynomial.normForm χ R) ∧
      ∀ ℓ N : ℕ, ℓ.Prime → (ℓ : k) ≠ 0 →
        Nonempty (Submodule.torsionBy ℤ (Stacks.Picard.picardDegree g hdim).ker ((ℓ : ℤ) ^ N) ≃+
          (Fin (2 * genus g) → ZMod (ℓ ^ N))) := by
  obtain ⟨A, _, _, E, F, _, hdimA, hpts, htan⟩ := exists_jacobianFrobenius_data p g hdim n hn Ψ hΨ
  have : IsCommMonObj A := isCommMonObj_of_isProper_of_geometricallyIntegral A
  let E' : Additive (𝟙_ (Over (Spec (.of k))) ⟶ A) ≃+ (Stacks.Picard.picardDegree g hdim).ker :=
    E.trans (picardDegreeZeroModelAddEquiv g hdim).symm
  have hE'v : ∀ y, ((E' y : (Stacks.Picard.picardDegree g hdim).ker) : Stacks.Picard.ofScheme X) =
      (Stacks.GluePicard.picardModelAddEquiv X.toRingedSpace).symm (E y).1 := fun y =>
    coe_picardDegreeZeroModelAddEquiv_symm g hdim (E y)
  have hE' : ∀ x, E' (Additive.ofMul (x ≫ F)) = u (E' (Additive.ofMul x)) := by
    intro x
    apply Subtype.ext
    rw [hu, hE'v, hE'v]
    exact hpts x
  obtain ⟨χ, hmon, hdeg, -, hR⟩ := Stacks.Groupoids.exists_endDegree_endPolyEval_eq_normForm A F
  refine ⟨χ, hmon, by rw [hdeg, hdimA], (hR Polynomial.X).symm ▸ Nat.cast_nonneg _, fun R hR0 => ?_,
    fun ℓ N hℓ hℓk => ?_⟩
  · have := Stacks.Groupoids.isMonHom_endPolyEval F R
    have hd : IsUnit ((R.coeff 0 : ℤ) : k) :=
      isUnit_iff_ne_zero.mpr fun h => hR0 ((CharP.intCast_eq_zero_iff k p _).mp h)
    have hcount := Stacks.Groupoids.natCard_comp_eq_one_eq_endDegree k A
      (Stacks.Groupoids.endPolyEval F R) (R.coeff 0) hd
      (fun s v => Stacks.Groupoids.comp_endPolyEval_of_comp_eq_one F _ (htan s v) R)
    have hequiv : {x : 𝟙_ (Over (Spec (.of k))) ⟶ A //
        x ≫ Stacks.Groupoids.endPolyEval F R = 1} ≃ (aeval (Stacks.Picard.asEnd u) R).ker :=
      Equiv.subtypeEquiv (Additive.ofMul.trans E'.toEquiv) fun x => by
        change _ ↔ aeval (Stacks.Picard.asEnd u) R (E' (Additive.ofMul x)) = 0
        rw [← endPolyEval_comp_eq_aeval F E' u hE' R x, AddEquiv.map_eq_zero_iff]
        exact ⟨fun h => by rw [h]; rfl, fun h => Additive.ofMul.injective h⟩
    rw [← Nat.card_congr hequiv, hcount]
    exact hR R
  · have hunit : IsUnit ((ℓ ^ N : ℕ) : k) := by
      rw [Nat.cast_pow]
      exact (isUnit_iff_ne_zero.mpr hℓk).pow N
    obtain ⟨e⟩ := Stacks.Groupoids.nonempty_torsionBy_addEquiv_of_isUnit k A (ℓ ^ N) hunit
    rw [hdimA] at e
    refine ⟨AddEquiv.trans ?_ e⟩
    exact
      { toFun := fun c => ⟨E'.symm c.1, by
          have hc := (Submodule.mem_torsionBy_iff _ _).mp c.2
          change (((ℓ ^ N : ℕ) : ℤ)) • E'.symm c.1 = 0
          rw [← map_zsmul, Nat.cast_pow, hc, map_zero]⟩
        invFun := fun x => ⟨E' x.1, by
          have hx : (((ℓ ^ N : ℕ) : ℤ)) • x.1 = 0 := x.2
          have hx' : ((ℓ : ℤ) ^ N) • x.1 = 0 := by exact_mod_cast hx
          rw [Submodule.mem_torsionBy_iff, ← map_zsmul, hx', map_zero]⟩
        left_inv := fun c => Subtype.ext (E'.apply_symm_apply c.1)
        right_inv := fun x => Subtype.ext (E'.symm_apply_apply x.1)
        map_add' := fun a b => Subtype.ext (map_add E'.symm a.1 b.1) }

end Stacks.Zeta
