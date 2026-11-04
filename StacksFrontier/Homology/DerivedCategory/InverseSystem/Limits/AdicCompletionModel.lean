module

public import StacksFrontier.Homology.DerivedCategory.InverseSystem.Limits.PseudoCoherent
public import StacksFrontier.RingTheory.AdicCompletion.EvalFactorPow

/-!
# The adic completion as the limit of the quotients by the powers of an ideal

For an ideal `I` of a commutative ring `Λ`, the `I`-adic completion `Λ^∧` together with its
evaluations `Λ^∧ → Λ/Iⁿ⁺¹` is a limit of the tower of rings `n ↦ Λ/Iⁿ⁺¹`, with no finiteness
or completeness hypothesis on `I`. This is the limit cone to which Stacks 0CQG
(`StacksDraft.DerivedInverseLimit.derivedLimit_isPerfect_and_baseChange_iso`) is applied in
order to produce a perfect complex over `Λ^∧` out of a compatible tower of perfect complexes
over the rings `Λ/Iⁿ⁺¹`.

## Main definitions

* `StacksDraft.DerivedInverseLimit.adicCompletionPowerCone`: the cone on
  `quotientPowerDiagram I` with vertex `Λ^∧`.
* `StacksDraft.DerivedInverseLimit.adicCompletionPowerConeIsLimit`: it is a limit cone.

## Main results

* `StacksDraft.DerivedInverseLimit.isIso_derivedBaseChangeComparison_of_kFlat`: derived base
  change along a chain map out of a K-flat complex whose adjoint is a quasi-isomorphism is an
  isomorphism.
* `StacksDraft.DerivedInverseLimit.exists_isBoundedAboveFiniteFree_adicCompletion_iso`: a
  complex of `Λ`-modules with K-flat reductions modulo `Iⁿ⁺¹`, the first one pseudo-coherent,
  has an adic model: a bounded above complex `F` of finite free `Λ^∧`-modules with
  `Λ/Iⁿ⁺¹ ⊗_{Λ^∧} F ≅ Λ/Iⁿ⁺¹ ⊗ N` in `D(Λ/Iⁿ⁺¹)` for all `n`.

## References

* [Stacks Project, Tag 0CQF](https://stacks.math.columbia.edu/tag/0CQF)
* [Stacks Project, Tag 09C5](https://stacks.math.columbia.edu/tag/09C5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace StacksDraft.DerivedInverseLimit

variable {Λ : Type u} [CommRing Λ] (I : Ideal Λ)

/-- The cone on the tower `n ↦ Λ/Iⁿ⁺¹` with vertex the `I`-adic completion, given by the
evaluations. -/
abbrev adicCompletionPowerCone : Cone (quotientPowerDiagram I) where
  pt := CommRingCat.of (AdicCompletion I Λ)
  π :=
    { app n := CommRingCat.ofHom (AdicCompletion.evalₐ I (n.unop + 1)).toRingHom
      naturality := fun _ _ f => by
        ext x
        exact (AdicCompletion.factorPow_evalₐ I
          (Nat.add_le_add_right (leOfHom f.unop) 1) x).symm }

/-- The ring maps `R → Λ/Iⁿ` attached to a cone over `n ↦ Λ/Iⁿ⁺¹`. -/
def adicCompletionPowerConeLiftAux (s : Cone (quotientPowerDiagram I)) (n : ℕ) :
    s.pt →+* Λ ⧸ I ^ n :=
  (Ideal.Quotient.factorPow I (Nat.le_succ n)).comp (s.π.app (op n)).hom

/-- For `m ≤ n`, the map `R → Λ/Iⁿ` followed by the projection `Λ/Iⁿ → Λ/Iᵐ` is the map
`R → Λ/Iᵐ`. -/
theorem adicCompletionPowerConeLiftAux_compat (s : Cone (quotientPowerDiagram I)) {m n : ℕ}
    (hle : m ≤ n) :
    (Ideal.Quotient.factorPow I hle).comp (adicCompletionPowerConeLiftAux I s n) =
      adicCompletionPowerConeLiftAux I s m := by
  have hw := congrArg CommRingCat.Hom.hom (s.w (homOfLE hle).op)
  ext x
  simp only [adicCompletionPowerConeLiftAux, RingHom.comp_apply]
  rw [← hw]
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective ((s.π.app (op n)).hom x)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, ← hy]
  rfl

/-- **The adic completion is the limit of the quotients by the powers of the ideal.** -/
def adicCompletionPowerConeIsLimit : IsLimit (adicCompletionPowerCone I) where
  lift s := CommRingCat.ofHom (AdicCompletion.liftRingHom I (adicCompletionPowerConeLiftAux I s)
    (adicCompletionPowerConeLiftAux_compat I s))
  fac s n := by
    ext x
    change AdicCompletion.evalₐ I (n.unop + 1) (AdicCompletion.liftRingHom I
      (adicCompletionPowerConeLiftAux I s) (adicCompletionPowerConeLiftAux_compat I s) x) = _
    rw [AdicCompletion.evalₐ_liftRingHom]
    have hw := congrArg CommRingCat.Hom.hom (s.w (homOfLE (Nat.le_succ n.unop)).op)
    simp only [adicCompletionPowerConeLiftAux, RingHom.comp_apply]
    rw [← hw]
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective ((s.π.app (op (n.unop + 1))).hom x)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, ← hy]
    rfl
  uniq s m hm := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    apply AdicCompletion.ext_evalₐ
    intro k
    change _ = AdicCompletion.evalₐ I k (AdicCompletion.liftRingHom I
      (adicCompletionPowerConeLiftAux I s) (adicCompletionPowerConeLiftAux_compat I s) x)
    rw [AdicCompletion.evalₐ_liftRingHom, ← AdicCompletion.factorPow_evalₐ I (Nat.le_succ k)]
    have := congrArg (fun g => g.hom x) (hm (op k))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
    simp only [adicCompletionPowerConeLiftAux, RingHom.comp_apply]
    exact congrArg (Ideal.Quotient.factorPow I (Nat.le_succ k)) this

section KFlat

attribute [local instance] HasDerivedCategory.standard

/-- **Derived base change along a chain map out of a K-flat complex.** Let `f : R → S` be a ring
map, `P` a K-flat complex of `R`-modules, `E` a complex of `S`-modules and `g : P ⟶ E` a chain map
over `R` whose adjoint `S ⊗_R P ⟶ E` is a quasi-isomorphism. Then the derived base change of the
localization of `g` is an isomorphism: derived extension of scalars is computed by termwise
extension of scalars on K-flat complexes. -/
theorem isIso_derivedBaseChangeComparison_of_kFlat {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (P : CochainComplex (ModuleCat.{u} R) ℤ) (hP : CochainComplex.KFlat.{u, u} P)
    (E : CochainComplex (ModuleCat.{u} S) ℤ)
    (g : P ⟶ ((ModuleCat.restrictScalars f).mapHomologicalComplex (ComplexShape.up ℤ)).obj E)
    (hg : QuasiIso (((mapHomologicalComplexAdjunction
      (ModuleCat.extendRestrictScalarsAdj.{u} f) (ComplexShape.up ℤ)).homEquiv _ _).symm g)) :
    IsIso (derivedBaseChangeComparison.{u, u, u} f (DerivedCategory.Q.map g ≫
      (ModuleCat.restrictScalars f).mapDerivedCategoryFactors.inv.app E)) := by
  let D := CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral.{u, u, u} f
  let adjD := @CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{u, u, u}
    R S _ _ f _ _ D.functor D.comparison D.isLeftDerived
  have hD : D.functor.IsLeftDerivedFunctor D.comparison
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) := D.isLeftDerived
  have hc : IsIso (D.comparison.app P) := D.comparison_isIso_of_kFlat P hP
  have hq : IsIso (DerivedCategory.Q.map (((mapHomologicalComplexAdjunction
      (ModuleCat.extendRestrictScalarsAdj.{u} f) (ComplexShape.up ℤ)).homEquiv _ _).symm g)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hg
  have key : (adjD.homEquiv _ _).symm (DerivedCategory.Q.map g ≫
      (ModuleCat.restrictScalars f).mapDerivedCategoryFactors.inv.app E) =
      D.comparison.app P ≫ DerivedCategory.Q.map (((mapHomologicalComplexAdjunction
        (ModuleCat.extendRestrictScalarsAdj.{u} f) (ComplexShape.up ℤ)).homEquiv _ _).symm g) := by
    have hcounit :=
      @CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction_counit_app.{u, u, u}
        R S _ _ f _ _ D.functor D.comparison D.isLeftDerived E
    rw [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc, hcounit,
      Adjunction.homEquiv_counit, Functor.map_comp]
    rw [← Category.assoc]
    exact (congrArg (· ≫ _) (D.comparison.naturality g)).trans (Category.assoc _ _ _)
  change IsIso ((adjD.homEquiv _ _).symm _)
  rw [key]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ hc hq

/-- The comparison `Λ/Iⁿ⁺¹ ⊗ (Λ/Iⁿ⁺² ⊗ N) ≅ Λ/Iⁿ⁺¹ ⊗ N` of the termwise reductions of a complex. -/
def reductionTransitionIso (N : CochainComplex (ModuleCat.{u} Λ) ℤ) (n : ℕ) :
    ((ModuleCat.extendScalars
        (Ideal.Quotient.factorPow I (Nat.le_succ (n + 1)))).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (((ModuleCat.extendScalars
          (Ideal.Quotient.mk (I ^ (n + 2)))).mapHomologicalComplex (ComplexShape.up ℤ)).obj N) ≅
      ((ModuleCat.extendScalars (Ideal.Quotient.mk (I ^ (n + 1)))).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj N :=
  ((Functor.mapHomologicalComplexCompIso (Iso.refl _) (ComplexShape.up ℤ)).app N) ≪≫
    (NatIso.mapHomologicalComplex ((ModuleCat.extendScalarsComp.{u, u} _ _).symm ≪≫
      eqToIso (congrArg (fun f => ModuleCat.extendScalars.{u, u, u} f)
        (show (Ideal.Quotient.factorPow I (Nat.le_succ (n + 1))).comp
            (Ideal.Quotient.mk (I ^ (n + 2))) = Ideal.Quotient.mk (I ^ (n + 1)) from
          RingHom.ext fun _ => rfl))) (ComplexShape.up ℤ)).app N

/-- **An adic model over the completion of a tower of reductions.** Let `N` be a complex of
`Λ`-modules whose reductions `Λ/Iⁿ ⊗ N` are K-flat, the first of them `Λ/I ⊗ N` being
pseudo-coherent. Then there is a bounded above complex `F` of finite free modules over the
`I`-adic completion `Λ^∧` such that `Λ/Iⁿ⁺¹ ⊗_{Λ^∧} F` and `Λ/Iⁿ⁺¹ ⊗ N` are isomorphic in
`D(Λ/Iⁿ⁺¹)` for every `n`: `F` represents the derived inverse limit of the tower of reductions
(Stacks 0CQF). -/
theorem exists_isBoundedAboveFiniteFree_adicCompletion_iso
    (N : CochainComplex (ModuleCat.{u} Λ) ℤ)
    (hN : ∀ n : ℕ, CochainComplex.KFlat.{u, u} (((ModuleCat.extendScalars
      (Ideal.Quotient.mk (I ^ (n + 1)))).mapHomologicalComplex (ComplexShape.up ℤ)).obj N))
    (hN₀ : PseudoCoherence.IsPseudoCoherent (DerivedCategory.Q.obj (((ModuleCat.extendScalars
      (Ideal.Quotient.mk (I ^ (0 + 1)))).mapHomologicalComplex (ComplexShape.up ℤ)).obj N))) :
    ∃ F : CochainComplex (ModuleCat.{u} (AdicCompletion I Λ)) ℤ,
      PseudoCoherence.IsBoundedAboveFiniteFree F ∧ ∀ n : ℕ,
        Nonempty (DerivedCategory.Q.obj (((ModuleCat.extendScalars
            (AdicCompletion.evalₐ I (n + 1)).toRingHom).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj F) ≅
          DerivedCategory.Q.obj (((ModuleCat.extendScalars
            (Ideal.Quotient.mk (I ^ (n + 1)))).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj N)) := by
  let red : ∀ n : ℕ, CochainComplex (ModuleCat.{u} (Λ ⧸ I ^ (n + 1))) ℤ := fun n =>
    ((ModuleCat.extendScalars (Ideal.Quotient.mk (I ^ (n + 1)))).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj N
  let Kₙ : ∀ n : ℕ, DerivedCategory (ModuleCat.{u} ((quotientPowerDiagram I).obj (op n))) :=
    fun n => DerivedCategory.Q.obj (red n)
  let q : ∀ n : ℕ, Λ ⧸ I ^ (n + 2) →+* Λ ⧸ I ^ (n + 1) := fun n =>
    Ideal.Quotient.factorPow I (Nat.le_succ (n + 1))
  let g : ∀ n : ℕ, red (n + 1) ⟶
      ((ModuleCat.restrictScalars (q n)).mapHomologicalComplex (ComplexShape.up ℤ)).obj (red n) :=
    fun n => (mapHomologicalComplexAdjunction (ModuleCat.extendRestrictScalarsAdj.{u} (q n))
      (ComplexShape.up ℤ)).homEquiv _ _ (reductionTransitionIso I N n).hom
  let φ : ∀ n : ℕ, Kₙ (n + 1) ⟶ (ModuleCat.restrictScalars
      ((quotientPowerDiagram I).map (homOfLE (Nat.le_succ n)).op).hom).mapDerivedCategory.obj
        (Kₙ n) := fun n =>
    DerivedCategory.Q.map (g n) ≫
      (ModuleCat.restrictScalars (q n)).mapDerivedCategoryFactors.inv.app (red n)
  have hBC : ∀ n : ℕ, IsIso (derivedBaseChangeComparison
      ((quotientPowerDiagram I).map (homOfLE (Nat.le_succ n)).op).hom (φ n)) := fun n => by
    refine isIso_derivedBaseChangeComparison_of_kFlat (q n) (red (n + 1)) (hN (n + 1)) (red n)
      (g n) ?_
    rw [Equiv.symm_apply_apply]
    infer_instance
  have hNil (n : ℕ) : IsNilpotent (RingHom.ker
      ((quotientPowerDiagram I).map (homOfLE (Nat.le_succ n)).op).hom) :=
    ⟨2, ker_factor_pow_eq_bot (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))
      (by rw [← pow_mul]; exact Ideal.pow_le_pow_right (by omega))⟩
  have h := derivedLimit_isPseudoCoherent_and_baseChange_iso.{u, u} (quotientPowerDiagram I)
    (adicCompletionPowerCone I) (adicCompletionPowerConeIsLimit I) Kₙ φ
    (fun n ↦ Ideal.Quotient.factor_surjective (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))))
    (fun n ↦ isLocallyNilpotent_of_isNilpotent _ (hNil n)) (Or.inr ⟨0, hN₀, fun n _ ↦ hNil n⟩)
    hBC
  let X : ℕ → DerivedCategory (ModuleCat.{u} (adicCompletionPowerCone I).pt) := fun n ↦
    (ModuleCat.restrictScalars
      ((adicCompletionPowerCone I).π.app (op n)).hom).mapDerivedCategory.obj (Kₙ n)
  let t : ∀ n : ℕ, X (n + 1) ⟶ X n := fun n ↦
    (ModuleCat.restrictScalars
        ((adicCompletionPowerCone I).π.app (op (n + 1))).hom).mapDerivedCategory.map (φ n) ≫
      (derivedRestrictScalarsComp ((adicCompletionPowerCone I).π.app (op (n + 1))).hom
        ((quotientPowerDiagram I).map (homOfLE (Nat.le_succ n)).op).hom
        ((adicCompletionPowerCone I).π.app (op n)).hom
        (congrArg CommRingCat.Hom.hom
          ((adicCompletionPowerCone I).w (homOfLE (Nat.le_succ n)).op)).symm).hom.app (Kₙ n)
  let : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} (adicCompletionPowerCone I).pt)) :=
    Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
  obtain ⟨K, p, δ, hT⟩ := Pretriangulated.distinguished_cocone_triangle₁
    (Pi.lift fun n : ℕ ↦ Pi.π X n - Pi.π X (n + 1) ≫ t n)
  obtain ⟨⟨F, hF, ⟨e⟩⟩, hbase⟩ := h K p δ hT
  obtain ⟨b, hb⟩ := hF.upperBound
  refine ⟨F, hF, fun n => ⟨?_⟩⟩
  have : ∀ i, Projective (F.X i) := fun i => by
    have := (hF.finiteFree i).2
    infer_instance
  let D := CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral.{u, u, u}
    (AdicCompletion.evalₐ I (n + 1)).toRingHom
  have := D.comparison_isIso_of_projective F b
  have := hbase n
  exact (asIso (D.comparison.app F)).symm ≪≫ D.functor.mapIso e ≪≫
    asIso (derivedBaseChangeComparison ((adicCompletionPowerCone I).π.app (op n)).hom
      (p ≫ Pi.π X n))

end KFlat

end StacksDraft.DerivedInverseLimit

end
