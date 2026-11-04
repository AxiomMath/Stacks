module

public import StacksFrontier.RingTheory.AdicCompletion.Comparison
public import StacksFrontier.RingTheory.Rig.NaiveCotangent

/-!
# The completed naive cotangent complex does not depend on the ideal of definition

Let `A` be a Noetherian ring and let `I`, `J` be two mutually cofinal ideals of `A`, that is
`I ^ a ≤ J` and `J ^ b ≤ I`.  Let `B` be an `A`-algebra which is an object of the category of
adically complete algebras of finite type modulo `I` and modulo `J`.  A completed polynomial
presentation of `B` over `(A, J)` transports to one over `(A, I)` along the comparison
isomorphism of the two completed polynomial algebras, and the two completed naive cotangent
complexes attached to the two presentations are isomorphic.

## Main definitions

* `Rig.doubleIsoDouble` — two two-term complexes with isomorphic terms and a commuting square
  are isomorphic.
* `Rig.IsAdicFiniteType` and `Rig.AdicFiniteTypeAlgebra.mk'` — the defining property of the
  objects of `Rig.AdicFiniteTypeAlgebra A I` as a predicate on commutative `A`-algebras, and
  the object it cuts out.  Two ideals then give two objects with the *same* carrier, which is
  what makes a comparison of their cotangent complexes expressible.
* `Rig.completedPolynomialEquiv` — the comparison isomorphism of completed polynomial
  algebras.
* `Rig.conjDerivation` — the conjugate of a derivation by that isomorphism.
* `Rig.CompletedPolynomialPresentation.transport` — the transported presentation, and
  `Rig.CompletedPolynomialPresentation.transportCotangentEquiv` the induced isomorphism of
  cotangent modules.

## Main results

* `Rig.CompletedPolynomialPresentation.completedPolynomialEquiv_partialDeriv` — the formal
  partial derivatives of the two presentations correspond, by the uniqueness clause of
  `Rig.CompletedNaiveCotangentComplex`.
* `Rig.CompletedPolynomialPresentation.transport_differential` — so do the differentials of
  the two completed naive cotangent complexes.
* `Rig.CompletedPolynomialPresentation.transportCochainComplexIso` — hence the two complexes
  are isomorphic, which is the independence assertion of Remark 0GBX.

## References

* [Stacks Project, Remark 0GBX](https://stacks.math.columbia.edu/tag/0GBX)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace Rig

universe u v

section Double

open CategoryTheory CategoryTheory.Limits

variable {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]
  {ι : Type*} {c : ComplexShape ι} {i₀ i₁ : ι} {Y₀ Y₁ Z₀ Z₁ : C}

/-- Two two-term complexes whose terms are isomorphic by a commuting square are isomorphic. -/
public def doubleIsoDouble (f : Y₀ ⟶ Y₁) (g : Z₀ ⟶ Z₁) (h : c.Rel i₀ i₁) (hne : i₀ ≠ i₁)
    (e₀ : Y₀ ≅ Z₀) (e₁ : Y₁ ≅ Z₁) (hcomm : e₀.hom ≫ g = f ≫ e₁.hom) :
    HomologicalComplex.double f h ≅ HomologicalComplex.double g h := by
  have hout : ∀ k, c.Rel i₁ k →
      (e₁.hom ≫ (HomologicalComplex.doubleXIso₁ g h hne).inv) ≫
        (HomologicalComplex.double g h).d i₁ k = 0 := by
    intro k _
    rw [HomologicalComplex.double_d_eq_zero₀ g h i₁ k hne.symm, comp_zero]
  have hsq : (e₀.hom ≫ (HomologicalComplex.doubleXIso₀ g h).inv) ≫
      (HomologicalComplex.double g h).d i₀ i₁ =
      f ≫ e₁.hom ≫ (HomologicalComplex.doubleXIso₁ g h hne).inv := by
    rw [HomologicalComplex.double_d g h hne]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc, hcomm, Category.assoc]
  let φ := HomologicalComplex.mkHomFromDouble h hne
    (e₀.hom ≫ (HomologicalComplex.doubleXIso₀ g h).inv)
    (e₁.hom ≫ (HomologicalComplex.doubleXIso₁ g h hne).inv) hsq hout
  haveI : ∀ j, IsIso (φ.f j) := by
    intro j
    by_cases h₀ : j = i₀
    · subst h₀
      dsimp only [φ]
      rw [HomologicalComplex.mkHomFromDouble_f₀]
      infer_instance
    · by_cases h₁ : j = i₁
      · subst h₁
        dsimp only [φ]
        rw [HomologicalComplex.mkHomFromDouble_f₁]
        infer_instance
      · let ε := (HomologicalComplex.isZero_double_X f h j h₀ h₁).iso
          (HomologicalComplex.isZero_double_X g h j h₀ h₁)
        have hε : φ.f j = ε.hom :=
          (HomologicalComplex.isZero_double_X f h j h₀ h₁).eq_of_src _ _
        rw [hε]
        infer_instance
  haveI := HomologicalComplex.Hom.isIso_of_components φ
  exact asIso φ

end Double

section

/-- Cofinality of a pair of ideals is inherited by their extensions along a ring
homomorphism. -/
public theorem pow_map_le_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    {I J : Ideal R} {a : ℕ} (ha : I ^ a ≤ J) : (I.map f) ^ a ≤ J.map f :=
  (Ideal.map_pow f I a).symm.le.trans (Ideal.map_mono ha)

variable {A : Type u} [CommRing A] {I J : Ideal A} {a b : ℕ}

/-- The comparison isomorphism between the completed polynomial algebras in `r` variables
attached to two mutually cofinal ideals of `A`. -/
public def completedPolynomialEquiv (ha : I ^ a ≤ J) (hb : J ^ b ≤ I) (r : ℕ) :
    AdicCompletion (I.map (MvPolynomial.C : A →+* MvPolynomial (Fin r) A))
        (MvPolynomial (Fin r) A) ≃ₐ[A]
      AdicCompletion (J.map (MvPolynomial.C : A →+* MvPolynomial (Fin r) A))
        (MvPolynomial (Fin r) A) :=
  AdicCompletion.compareAlgEquiv A (pow_map_le_map _ ha) (pow_map_le_map _ hb)

/-- The comparison isomorphism is the identity on polynomials. -/
@[simp]
public theorem completedPolynomialEquiv_algebraMap (ha : I ^ a ≤ J) (hb : J ^ b ≤ I) (r : ℕ)
    (f : MvPolynomial (Fin r) A) :
    completedPolynomialEquiv ha hb r
        (algebraMap (MvPolynomial (Fin r) A) _ f) = algebraMap _ _ f :=
  AdicCompletion.compareAlgEquiv_algebraMap A _ _ f

/-- The inverse comparison isomorphism is the identity on polynomials. -/
@[simp]
public theorem completedPolynomialEquiv_symm_algebraMap (ha : I ^ a ≤ J) (hb : J ^ b ≤ I)
    (r : ℕ) (f : MvPolynomial (Fin r) A) :
    (completedPolynomialEquiv ha hb r).symm
        (algebraMap (MvPolynomial (Fin r) A) _ f) = algebraMap _ _ f :=
  (completedPolynomialEquiv ha hb r).injective (by
    rw [AlgEquiv.apply_symm_apply, completedPolynomialEquiv_algebraMap])

/-- The level-`n` reduction of the comparison isomorphism of completed polynomial algebras. -/
public theorem evalₐ_completedPolynomialEquiv (ha : I ^ a ≤ J) (hb : J ^ b ≤ I) (r n : ℕ)
    (x : AdicCompletion (I.map (MvPolynomial.C : A →+* MvPolynomial (Fin r) A))
      (MvPolynomial (Fin r) A)) :
    AdicCompletion.evalₐ (J.map (MvPolynomial.C : A →+* MvPolynomial (Fin r) A)) n
        (completedPolynomialEquiv ha hb r x) =
      Ideal.Quotient.factor (AdicCompletion.pow_mul_le_pow_of_pow_le
          ((Ideal.pow_le_pow_right (Nat.le_succ a)).trans
            (pow_map_le_map (MvPolynomial.C : A →+* MvPolynomial (Fin r) A) ha)) n)
        (AdicCompletion.evalₐ (I.map (MvPolynomial.C : A →+* MvPolynomial (Fin r) A))
          ((a + 1) * n) x) :=
  AdicCompletion.evalₐ_compareAlgEquiv A _ _ n x

/-- The comparison isomorphism of completed polynomial algebras is continuous for the two
inverse-limit topologies. -/
public theorem continuous_completedPolynomialEquiv (ha : I ^ a ≤ J) (hb : J ^ b ≤ I) (r : ℕ) :
    @Continuous _ _
      (RestrictedPowerSeries.polynomialCompletionLimitTopology I (Fin r))
      (RestrictedPowerSeries.polynomialCompletionLimitTopology J (Fin r))
      (completedPolynomialEquiv ha hb r) := by
  let _ : ∀ n : ℕ, TopologicalSpace (MvPolynomial (Fin r) A ⧸
    (I.map (MvPolynomial.C : A →+* MvPolynomial (Fin r) A)) ^ n) := fun _ ↦ ⊥
  let _ : ∀ n : ℕ, TopologicalSpace (MvPolynomial (Fin r) A ⧸
    (J.map (MvPolynomial.C : A →+* MvPolynomial (Fin r) A)) ^ n) := fun _ ↦ ⊥
  let _ : ∀ n : ℕ, DiscreteTopology (MvPolynomial (Fin r) A ⧸
    (I.map (MvPolynomial.C : A →+* MvPolynomial (Fin r) A)) ^ n) := fun _ ↦ ⟨rfl⟩
  let _ : TopologicalSpace (AdicCompletion
      (I.map (MvPolynomial.C : A →+* MvPolynomial (Fin r) A)) (MvPolynomial (Fin r) A)) :=
    RestrictedPowerSeries.polynomialCompletionLimitTopology I (Fin r)
  let _ : TopologicalSpace (AdicCompletion
      (J.map (MvPolynomial.C : A →+* MvPolynomial (Fin r) A)) (MvPolynomial (Fin r) A)) :=
    RestrictedPowerSeries.polynomialCompletionLimitTopology J (Fin r)
  have hp : Continuous (fun f : AdicCompletion
      (I.map (MvPolynomial.C : A →+* MvPolynomial (Fin r) A)) (MvPolynomial (Fin r) A) ↦
      fun k : ℕ ↦ AdicCompletion.evalₐ _ k f) := continuous_induced_dom
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro n
  have h1 : Continuous (fun x : AdicCompletion
      (I.map (MvPolynomial.C : A →+* MvPolynomial (Fin r) A)) (MvPolynomial (Fin r) A) ↦
      AdicCompletion.evalₐ (I.map (MvPolynomial.C : A →+* MvPolynomial (Fin r) A))
        ((a + 1) * n) x) := (continuous_apply ((a + 1) * n)).comp hp
  have h2 : Continuous (Ideal.Quotient.factor (AdicCompletion.pow_mul_le_pow_of_pow_le
      ((Ideal.pow_le_pow_right (Nat.le_succ a)).trans
        (pow_map_le_map (MvPolynomial.C : A →+* MvPolynomial (Fin r) A) ha)) n)) :=
    continuous_of_discreteTopology
  exact (h2.comp h1).congr fun x ↦ (evalₐ_completedPolynomialEquiv ha hb r n x).symm

/-- The inverse comparison isomorphism of completed polynomial algebras is continuous for the
two inverse-limit topologies. -/
public theorem continuous_completedPolynomialEquiv_symm (ha : I ^ a ≤ J) (hb : J ^ b ≤ I)
    (r : ℕ) :
    @Continuous _ _
      (RestrictedPowerSeries.polynomialCompletionLimitTopology J (Fin r))
      (RestrictedPowerSeries.polynomialCompletionLimitTopology I (Fin r))
      (completedPolynomialEquiv ha hb r).symm :=
  continuous_completedPolynomialEquiv hb ha r

/-- The conjugate, by the comparison isomorphism, of a derivation of the `J`-adic completed
polynomial algebra. -/
public def conjDerivation (ha : I ^ a ≤ J) (hb : J ^ b ≤ I) (r : ℕ)
    (d : Derivation A
      (AdicCompletion (J.map (MvPolynomial.C : A →+* MvPolynomial (Fin r) A))
        (MvPolynomial (Fin r) A))
      (AdicCompletion (J.map (MvPolynomial.C : A →+* MvPolynomial (Fin r) A))
        (MvPolynomial (Fin r) A))) :
    Derivation A
      (AdicCompletion (I.map (MvPolynomial.C : A →+* MvPolynomial (Fin r) A))
        (MvPolynomial (Fin r) A))
      (AdicCompletion (I.map (MvPolynomial.C : A →+* MvPolynomial (Fin r) A))
        (MvPolynomial (Fin r) A)) :=
  Derivation.mk'
    ((completedPolynomialEquiv ha hb r).symm.toLinearEquiv.toLinearMap.comp
      (d.toLinearMap.comp (completedPolynomialEquiv ha hb r).toLinearEquiv.toLinearMap))
    (by
      have hval : ∀ z, ((completedPolynomialEquiv ha hb r).symm.toLinearEquiv.toLinearMap.comp
          (d.toLinearMap.comp (completedPolynomialEquiv ha hb r).toLinearEquiv.toLinearMap)) z =
          (completedPolynomialEquiv ha hb r).symm (d (completedPolynomialEquiv ha hb r z)) :=
        fun _ ↦ rfl
      intro x y
      rw [hval, hval, hval, map_mul, Derivation.leibniz]
      simp)

/-- The conjugate derivation is `d` conjugated by the comparison isomorphism. -/
@[simp]
public theorem conjDerivation_apply (ha : I ^ a ≤ J) (hb : J ^ b ≤ I) (r : ℕ)
    (d : Derivation A
      (AdicCompletion (J.map (MvPolynomial.C : A →+* MvPolynomial (Fin r) A))
        (MvPolynomial (Fin r) A))
      (AdicCompletion (J.map (MvPolynomial.C : A →+* MvPolynomial (Fin r) A))
        (MvPolynomial (Fin r) A)))
    (x : AdicCompletion (I.map (MvPolynomial.C : A →+* MvPolynomial (Fin r) A))
      (MvPolynomial (Fin r) A)) :
    conjDerivation ha hb r d x =
      (completedPolynomialEquiv ha hb r).symm (d (completedPolynomialEquiv ha hb r x)) :=
  rfl

/-- The conjugate of a continuous derivation is continuous. -/
public theorem continuous_conjDerivation (ha : I ^ a ≤ J) (hb : J ^ b ≤ I) (r : ℕ)
    (d : Derivation A
      (AdicCompletion (J.map (MvPolynomial.C : A →+* MvPolynomial (Fin r) A))
        (MvPolynomial (Fin r) A))
      (AdicCompletion (J.map (MvPolynomial.C : A →+* MvPolynomial (Fin r) A))
        (MvPolynomial (Fin r) A)))
    (hd : @Continuous _ _
      (RestrictedPowerSeries.polynomialCompletionLimitTopology J (Fin r))
      (RestrictedPowerSeries.polynomialCompletionLimitTopology J (Fin r)) d) :
    @Continuous _ _
      (RestrictedPowerSeries.polynomialCompletionLimitTopology I (Fin r))
      (RestrictedPowerSeries.polynomialCompletionLimitTopology I (Fin r))
      (conjDerivation ha hb r d) := by
  let _ : TopologicalSpace (AdicCompletion
      (I.map (MvPolynomial.C : A →+* MvPolynomial (Fin r) A)) (MvPolynomial (Fin r) A)) :=
    RestrictedPowerSeries.polynomialCompletionLimitTopology I (Fin r)
  let _ : TopologicalSpace (AdicCompletion
      (J.map (MvPolynomial.C : A →+* MvPolynomial (Fin r) A)) (MvPolynomial (Fin r) A)) :=
    RestrictedPowerSeries.polynomialCompletionLimitTopology J (Fin r)
  exact (continuous_completedPolynomialEquiv_symm ha hb r).comp
    (hd.comp (continuous_completedPolynomialEquiv ha hb r))

/-- The conjugate of a derivation which is the formal partial derivative on polynomials is
again the formal partial derivative on polynomials. -/
public theorem conjDerivation_algebraMap (ha : I ^ a ≤ J) (hb : J ^ b ≤ I) (r : ℕ)
    (d : Derivation A
      (AdicCompletion (J.map (MvPolynomial.C : A →+* MvPolynomial (Fin r) A))
        (MvPolynomial (Fin r) A))
      (AdicCompletion (J.map (MvPolynomial.C : A →+* MvPolynomial (Fin r) A))
        (MvPolynomial (Fin r) A)))
    (i : Fin r)
    (hd : ∀ f : MvPolynomial (Fin r) A, d (algebraMap _ _ f) =
      algebraMap _ _ (MvPolynomial.pderiv i f))
    (f : MvPolynomial (Fin r) A) :
    conjDerivation ha hb r d (algebraMap _ _ f) =
      algebraMap _ _ (MvPolynomial.pderiv i f) := by
  rw [conjDerivation_apply, completedPolynomialEquiv_algebraMap, hd,
    completedPolynomialEquiv_symm_algebraMap]

end

section

variable {A : Type u} [CommRing A]

/-- The defining property of the objects of `Rig.AdicFiniteTypeAlgebra A I`, as a predicate on
commutative `A`-algebras. -/
public abbrev IsAdicFiniteType (I : Ideal A) (X : CommAlgCat.{v} A) : Prop :=
  IsAdicComplete (I.map (algebraMap A X)) X ∧
    Algebra.FiniteType (A ⧸ I) (X ⧸ I.map (algebraMap A X))

/-- The object of `Rig.AdicFiniteTypeAlgebra A I` on a commutative `A`-algebra satisfying the
defining property.  Unlike `Rig.AdicFiniteTypeAlgebra.of` this records the underlying
object, so two ideals give two objects with the same carrier. -/
public abbrev AdicFiniteTypeAlgebra.mk' {I : Ideal A} (X : CommAlgCat.{v} A)
    (p : IsAdicFiniteType I X) : AdicFiniteTypeAlgebra.{u, v} A I := ⟨X, p⟩

end

namespace CompletedPolynomialPresentation

variable {A : Type u} [CommRing A] {I J : Ideal A} {a b : ℕ} {X : CommAlgCat.{v} A}

/-- A completed polynomial presentation over `(A, J)` transported to one over `(A, I)` along
the comparison isomorphism of the completed polynomial algebras. -/
public def transport (pI : IsAdicFiniteType I X) (pJ : IsAdicFiniteType J X)
    (P : CompletedPolynomialPresentation J (AdicFiniteTypeAlgebra.mk' X pJ))
    (ha : I ^ a ≤ J) (hb : J ^ b ≤ I) :
    CompletedPolynomialPresentation I (AdicFiniteTypeAlgebra.mk' X pI) :=
  let F := P.toAlgHom.comp (completedPolynomialEquiv ha hb P.variableCount).toAlgHom
  have hF : Function.Surjective F :=
    P.toAlgHom_surjective.comp (completedPolynomialEquiv ha hb P.variableCount).surjective
  { variableCount := P.variableCount
    ideal := RingHom.ker F.toRingHom
    quotientEquiv := Ideal.quotientKerAlgEquivOfSurjective hF }

/-- The transported presentation has the same number of variables as the original one. -/
@[simp]
public theorem transport_variableCount (pI : IsAdicFiniteType I X) (pJ : IsAdicFiniteType J X)
    (P : CompletedPolynomialPresentation J (AdicFiniteTypeAlgebra.mk' X pJ))
    (ha : I ^ a ≤ J) (hb : J ^ b ≤ I) :
    (transport pI pJ P ha hb).variableCount = P.variableCount := rfl

/-- The structure map of the transported presentation is the structure map of the original
one, precomposed with the comparison isomorphism. -/
public theorem transport_toAlgHom_apply (pI : IsAdicFiniteType I X)
    (pJ : IsAdicFiniteType J X)
    (P : CompletedPolynomialPresentation J (AdicFiniteTypeAlgebra.mk' X pJ))
    (ha : I ^ a ≤ J) (hb : J ^ b ≤ I)
    (x : AdicCompletion (I.map (MvPolynomial.C : A →+* MvPolynomial (Fin P.variableCount) A))
      (MvPolynomial (Fin P.variableCount) A)) :
    (transport pI pJ P ha hb).toAlgHom x =
      P.toAlgHom (completedPolynomialEquiv ha hb P.variableCount x) :=
  rfl

section

variable (pI : IsAdicFiniteType I X) (pJ : IsAdicFiniteType J X)
    (P : CompletedPolynomialPresentation J (AdicFiniteTypeAlgebra.mk' X pJ))
    (ha : I ^ a ≤ J) (hb : J ^ b ≤ I)

/-- The comparison isomorphism, as a map between the extensions underlying the transported
presentation and the original one. -/
public def transportExtensionHom :
    (transport pI pJ P ha hb).extension.Hom P.extension where
  toRingHom := (completedPolynomialEquiv ha hb P.variableCount).toRingEquiv.toRingHom
  toRingHom_algebraMap x := (completedPolynomialEquiv ha hb P.variableCount).commutes x
  algebraMap_toRingHom x := (transport_toAlgHom_apply pI pJ P ha hb x).symm

/-- The inverse comparison isomorphism, as a map between the extensions underlying the
original presentation and the transported one. -/
public def transportExtensionHomSymm :
    P.extension.Hom (transport pI pJ P ha hb).extension where
  toRingHom := (completedPolynomialEquiv ha hb P.variableCount).symm.toRingEquiv.toRingHom
  toRingHom_algebraMap x := (completedPolynomialEquiv ha hb P.variableCount).symm.commutes x
  algebraMap_toRingHom x :=
    (transport_toAlgHom_apply pI pJ P ha hb
        ((completedPolynomialEquiv ha hb P.variableCount).symm x)).trans
      (congrArg P.toAlgHom
        ((completedPolynomialEquiv ha hb P.variableCount).apply_symm_apply x))

/-- The comparison isomorphism induces an isomorphism between the cotangent modules of the
transported presentation and of the original one. -/
public def transportCotangentEquiv :
    (transport pI pJ P ha hb).extension.Cotangent ≃ₗ[X] P.extension.Cotangent :=
  LinearEquiv.ofLinearMap
    (Algebra.Extension.Cotangent.map (transportExtensionHom pI pJ P ha hb))
    (Algebra.Extension.Cotangent.map (transportExtensionHomSymm pI pJ P ha hb))
    (by
      refine LinearMap.ext fun y ↦ ?_
      obtain ⟨z, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective y
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq,
        Algebra.Extension.Cotangent.map_mk]
      exact congrArg Algebra.Extension.Cotangent.mk (Subtype.ext
        ((completedPolynomialEquiv ha hb P.variableCount).apply_symm_apply z.1)))
    (by
      refine LinearMap.ext fun y ↦ ?_
      obtain ⟨z, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective y
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq,
        Algebra.Extension.Cotangent.map_mk]
      exact congrArg Algebra.Extension.Cotangent.mk (Subtype.ext
        ((completedPolynomialEquiv ha hb P.variableCount).symm_apply_apply z.1)))

/-- The cotangent isomorphism sends the class of `z` to the class of its image under the
comparison isomorphism. -/
@[simp]
public theorem transportCotangentEquiv_mk (z : (transport pI pJ P ha hb).extension.ker)
    (hz : completedPolynomialEquiv ha hb P.variableCount z.1 ∈ P.extension.ker) :
    transportCotangentEquiv pI pJ P ha hb (Algebra.Extension.Cotangent.mk z) =
      Algebra.Extension.Cotangent.mk
        ⟨completedPolynomialEquiv ha hb P.variableCount z.1, hz⟩ :=
  Algebra.Extension.Cotangent.map_mk (transportExtensionHom pI pJ P ha hb) z

end

section

variable [IsNoetherianRing A] (pI : IsAdicFiniteType I X) (pJ : IsAdicFiniteType J X)
    (P : CompletedPolynomialPresentation J (AdicFiniteTypeAlgebra.mk' X pJ))
    (ha : I ^ a ≤ J) (hb : J ^ b ≤ I)

/-- The formal partial derivatives attached to the transported presentation and to the
original one correspond under the comparison isomorphism.  This is the uniqueness clause of
`Rig.CompletedNaiveCotangentComplex`: conjugating a continuous derivation extending the formal
partial derivative on polynomials by the comparison isomorphism gives such a derivation
again. -/
public theorem completedPolynomialEquiv_partialDeriv (i : Fin P.variableCount)
    (g : AdicCompletion (I.map (MvPolynomial.C : A →+* MvPolynomial (Fin P.variableCount) A))
      (MvPolynomial (Fin P.variableCount) A)) :
    completedPolynomialEquiv ha hb P.variableCount
        ((completedNaiveCotangentComplex (AdicFiniteTypeAlgebra.mk' X pI)
          (transport pI pJ P ha hb)).partialDeriv i g) =
      (completedNaiveCotangentComplex (AdicFiniteTypeAlgebra.mk' X pJ) P).partialDeriv i
        (completedPolynomialEquiv ha hb P.variableCount g) := by
  have huniq := (completedNaiveCotangentComplex (AdicFiniteTypeAlgebra.mk' X pI)
      (transport pI pJ P ha hb)).partialDeriv_unique i
    (conjDerivation ha hb P.variableCount
      ((completedNaiveCotangentComplex (AdicFiniteTypeAlgebra.mk' X pJ) P).partialDeriv i))
    (continuous_conjDerivation ha hb P.variableCount _
      ((completedNaiveCotangentComplex (AdicFiniteTypeAlgebra.mk' X pJ) P).partialDeriv_continuous
        i))
    (fun f ↦ conjDerivation_algebraMap ha hb P.variableCount _ i
      ((completedNaiveCotangentComplex (AdicFiniteTypeAlgebra.mk' X pJ) P).partialDeriv_polynomial
        i) f)
  refine (congrArg (fun z ↦ completedPolynomialEquiv ha hb P.variableCount z)
    (DFunLike.congr_fun huniq g).symm).trans ?_
  exact (completedPolynomialEquiv ha hb P.variableCount).apply_symm_apply _

/-- The differentials of the two completed naive cotangent complexes correspond under the
isomorphism of the cotangent modules. -/
public theorem transport_differential (y : (transport pI pJ P ha hb).extension.Cotangent) :
    (completedNaiveCotangentComplex (AdicFiniteTypeAlgebra.mk' X pJ) P).differential
        (transportCotangentEquiv pI pJ P ha hb y) =
      (completedNaiveCotangentComplex (AdicFiniteTypeAlgebra.mk' X pI)
        (transport pI pJ P ha hb)).differential y := by
  obtain ⟨z, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective y
  have h1 : transportCotangentEquiv pI pJ P ha hb (Algebra.Extension.Cotangent.mk z) =
      Algebra.Extension.Cotangent.map (transportExtensionHom pI pJ P ha hb)
        (Algebra.Extension.Cotangent.mk z) := rfl
  rw [h1, Algebra.Extension.Cotangent.map_mk,
    (completedNaiveCotangentComplex (AdicFiniteTypeAlgebra.mk' X pJ) P).differential_mk,
    (completedNaiveCotangentComplex (AdicFiniteTypeAlgebra.mk' X pI)
      (transport pI pJ P ha hb)).differential_mk]
  funext i
  exact (congrArg (fun w ↦ P.toAlgHom w)
      (completedPolynomialEquiv_partialDeriv pI pJ P ha hb i z.1).symm).trans
    (transport_toAlgHom_apply pI pJ P ha hb _).symm

/-- **Stacks Project, Remark 0GBX.** The completed naive cotangent complexes attached to a
presentation over `(A, J)` and to its transport over `(A, I)` are isomorphic: the complex
`NL^∧_{B/A}` does not depend on the ideal of definition. -/
public def transportCochainComplexIso :
    (completedNaiveCotangentComplex (AdicFiniteTypeAlgebra.mk' X pI)
        (transport pI pJ P ha hb)).cochainComplex ≅
      (completedNaiveCotangentComplex (AdicFiniteTypeAlgebra.mk' X pJ) P).cochainComplex :=
  doubleIsoDouble _ _ (show (ComplexShape.up ℤ).Rel (-1) 0 from rfl) (by decide)
    (ULift.moduleEquiv.trans
      ((transportCotangentEquiv pI pJ P ha hb).trans ULift.moduleEquiv.symm)).toModuleIso
    (Iso.refl _)
    (by
      refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
      exact congrArg ULift.up (transport_differential pI pJ P ha hb x.down))

end

end CompletedPolynomialPresentation

end Rig

end
