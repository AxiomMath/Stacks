module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.AssertionsRetract
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.FiniteDirectImageAssertions

/-!
# The eight assertions with finiteness independent of constructibility

Assertions (4) and (5) of Stacks Tag 03SC assert finiteness of cohomology of *constructible*
sheaves. We consider the eight assertions together with finiteness of all cohomology groups under
the torsion, resp. properness, condition alone, and show that this strong form is preserved by
retracts, short exact sequences and finite direct images without any constructibility hypothesis.

## Main definitions

* `Stacks.EtaleCohomology.StrongTorsionCurveAssertions`: the eight assertions together with the
  two finiteness statements without constructibility.

## Main results

* `StrongTorsionCurveAssertions.of_retract`, `.of_shortExact`, `.of_directImage`, `.of_iso`,
  `.of_isZero`: the closure properties.
* `StrongTorsionCurveAssertions.of_isConstructibleEtaleSheaf`: for a constructible sheaf the eight
  assertions already give the strong form.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian ZeroObject
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-- The eight assertions of Tag 03SC, together with finiteness of every cohomology group when the
sheaf is torsion prime to the characteristic, resp. when `X` is proper, without the
constructibility hypothesis of assertions (4) and (5). -/
structure StrongTorsionCurveAssertions {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) : Prop where
  /-- The eight assertions of Tag 03SC hold for `F`. -/
  toTorsionCurveAssertions : TorsionCurveAssertions f F
  /-- If `F` is torsion prime to the characteristic of `k`, every cohomology group of `F` is
  finite. -/
  finite_of_isPrimeToCharacteristicTorsion :
    Stacks.Torsion.IsPrimeToCharacteristicTorsion X.smallEtaleTopology (ringExpChar k) F →
      ∀ q : ℕ, Finite (Sheaf.H.{u + 1} F q)
  /-- If `f` is proper, every cohomology group of `F` is finite. -/
  finite_of_isProper : IsProper f → ∀ q : ℕ, Finite (Sheaf.H.{u + 1} F q)

namespace StrongTorsionCurveAssertions

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- For a constructible sheaf the eight assertions give the strong form. -/
theorem of_isConstructibleEtaleSheaf {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (h : TorsionCurveAssertions f F) (hF : IsConstructibleSmallEtaleSheaf F) :
    StrongTorsionCurveAssertions f F :=
  ⟨h, fun ht => h.finite_of_isPrimeToCharacteristicTorsion hF ht,
    fun hp => h.finite_of_isProper hp hF⟩

/-- The zero sheaf. -/
theorem of_isZero {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (hF : IsZero F) :
    StrongTorsionCurveAssertions f F := by
  have : ∀ q, Subsingleton (Sheaf.H.{u + 1} F q) := fun q =>
    subsingleton_ext_of_isZero_right _ hF q
  exact ⟨TorsionCurveAssertions.of_isZero f hF, fun _ q => Finite.of_subsingleton,
    fun _ q => Finite.of_subsingleton⟩

/-- **The strong assertions pass to a retract** (the trace step of Tag 03SD), for sheaves killed
by a prime. -/
theorem of_retract {ℓ : ℕ} (hℓ : ℓ.Prime)
    {A G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (ι : A ⟶ G)
    (p : G ⟶ A) (hip : ι ≫ p = 𝟙 A) (hA : ℓ • 𝟙 A = 0) (hG : ℓ • 𝟙 G = 0)
    (h : StrongTorsionCurveAssertions f G) :
    StrongTorsionCurveAssertions f A := by
  by_cases hz : IsZero A
  · exact of_isZero f hz
  have hp := fun p' => isPrimePowerTorsion_of_nsmul_id_eq_zero_of_not_isZero hℓ hA hG hz p'
  have ht := isPrimeToCharacteristicTorsion_of_nsmul_id_eq_zero_of_not_isZero hℓ hA hG hz
    (ringExpChar k)
  have hinj := fun q => TorsionCurveAssertions.injective_comp_mk₀_of_retract ι p hip (M :=
    (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))) q
  have h' := h.toTorsionCurveAssertions
  have hfin₁ : Stacks.Torsion.IsPrimeToCharacteristicTorsion X.smallEtaleTopology
      (ringExpChar k) A → ∀ q, Finite (Sheaf.H.{u + 1} A q) := fun htA q =>
    have := h.finite_of_isPrimeToCharacteristicTorsion (ht htA) q
    Finite.of_injective _ (hinj q)
  have hfin₂ : IsProper f → ∀ q, Finite (Sheaf.H.{u + 1} A q) := fun hf q =>
    have := h.finite_of_isProper hf q
    Finite.of_injective _ (hinj q)
  refine ⟨
    { vanishing := fun q hq => have := h'.vanishing q hq; (hinj q).subsingleton
      vanishing_of_isAffine := fun hX q hq =>
        have := h'.vanishing_of_isAffine hX q hq; (hinj q).subsingleton
      vanishing_of_isPrimePowerTorsion := fun p' hp' hp0 hF q hq =>
        have := h'.vanishing_of_isPrimePowerTorsion p' hp' hp0 (hp p' hF) q hq
        (hinj q).subsingleton
      finite_of_isPrimeToCharacteristicTorsion := fun _ htA q => hfin₁ htA q
      finite_of_isProper := fun hf _ q => hfin₂ hf q
      bijective_of_isPrimeToCharacteristicTorsion := fun htA k' _ _ _ _ q =>
        etaleCohomologyRestrictionMap_bijective_of_retract.{u, u + 1, u + 1} _ ι p hip
          (h'.bijective_of_isPrimeToCharacteristicTorsion (ht htA) k' q)
      bijective_of_isProper := fun hf k' _ _ _ _ q =>
        etaleCohomologyRestrictionMap_bijective_of_retract.{u, u + 1, u + 1} _ ι p hip
          (h'.bijective_of_isProper hf k' q)
      surjective_restriction := fun U _ y => by
        obtain ⟨x, hx⟩ := h'.surjective_restriction U
          (y.comp (Ext.mk₀ ((etaleAbelianInverseImage.{u, u + 1} U.ι).map ι)) (add_zero 2))
        refine ⟨x.comp (Ext.mk₀ p) (add_zero 2), ?_⟩
        rw [etaleCohomologyRestrictionMap_comp_mk₀.{u, u + 1, u + 1}, hx,
          Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, ← CategoryTheory.Functor.map_comp,
          hip, CategoryTheory.Functor.map_id, Ext.comp_mk₀_id] }, hfin₁, hfin₂⟩

/-- **Stacks Tag 0A5C for the strong assertions.** -/
theorem of_shortExact [IsNoetherian X]
    {S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})} (hS : S.ShortExact)
    (h₁ : StrongTorsionCurveAssertions f S.X₁) (h₃ : StrongTorsionCurveAssertions f S.X₃) :
    StrongTorsionCurveAssertions f S.X₂ where
  toTorsionCurveAssertions := TorsionCurveAssertions.of_shortExact f hS
    h₁.toTorsionCurveAssertions h₃.toTorsionCurveAssertions
  finite_of_isPrimeToCharacteristicTorsion ht q := by
    have ht' := isPrimeToCharacteristicTorsion_of_shortExact (ringExpChar k) hS ht
    have := h₁.finite_of_isPrimeToCharacteristicTorsion ht'.1 q
    have := h₃.finite_of_isPrimeToCharacteristicTorsion ht'.2 q
    exact finite_sheafCohomology_X₂_of_shortExact hS q
  finite_of_isProper hf q := by
    have := h₁.finite_of_isProper hf q
    have := h₃.finite_of_isProper hf q
    exact finite_sheafCohomology_X₂_of_shortExact hS q

/-- The strong assertions are invariant under isomorphism. -/
theorem of_iso [IsNoetherian X] {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (e : F ≅ G) (h : StrongTorsionCurveAssertions f F) : StrongTorsionCurveAssertions f G := by
  have hS : (ShortComplex.mk e.hom (0 : G ⟶ 0) (by simp)).ShortExact :=
    ShortComplex.Splitting.shortExact
      { r := e.inv
        s := 0
        f_r := by simp
        s_g := (isZero_zero _).eq_of_tgt _ _
        id := by simp }
  exact of_shortExact f hS h (of_isZero f (isZero_zero _))

end StrongTorsionCurveAssertions

namespace StrongTorsionCurveAssertions

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (fY : Y ⟶ Spec (.of k)) (π : X ⟶ Y)
  [IsFinite π]
  [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- **Stacks Tag 0A5D for the strong assertions**, for a sheaf killed by a prime. -/
theorem of_directImage {ℓ : ℕ} (hℓ : ℓ.Prime)
    {G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (hℓG : ℓ • 𝟙 G = 0) (h : StrongTorsionCurveAssertions (π ≫ fY) G) :
    StrongTorsionCurveAssertions fY ((etaleAbelianDirectImage.{u, u + 1} π).obj G) := by
  by_cases hz : IsZero ((etaleAbelianDirectImage.{u, u + 1} π).obj G)
  · exact of_isZero fY hz
  have h₁ : ℓ • 𝟙 ((etaleAbelianDirectImage.{u, u + 1} π).obj G) = 0 := by
    rw [← CategoryTheory.Functor.map_id, ← Functor.map_nsmul, hℓG, Functor.map_zero]
  have hp := fun p => isPrimePowerTorsion_of_nsmul_id_eq_zero_of_not_isZero hℓ h₁ hℓG hz p
  have ht := isPrimeToCharacteristicTorsion_of_nsmul_id_eq_zero_of_not_isZero hℓ h₁ hℓG hz
    (ringExpChar k)
  have h' := h.toTorsionCurveAssertions
  let e : ∀ q, Sheaf.H.{u + 1} ((etaleAbelianDirectImage.{u, u + 1} π).obj G) q ≃
      Sheaf.H.{u + 1} G q := fun q => Equiv.ofBijective _ (bijective_edgeMap π q G)
  have hfin₁ : Stacks.Torsion.IsPrimeToCharacteristicTorsion Y.smallEtaleTopology
      (ringExpChar k) ((etaleAbelianDirectImage.{u, u + 1} π).obj G) →
      ∀ q, Finite (Sheaf.H.{u + 1} ((etaleAbelianDirectImage.{u, u + 1} π).obj G) q) :=
    fun htF q =>
      (Equiv.finite_iff (e q)).mpr (h.finite_of_isPrimeToCharacteristicTorsion (ht htF) q)
  have hfin₂ : IsProper fY →
      ∀ q, Finite (Sheaf.H.{u + 1} ((etaleAbelianDirectImage.{u, u + 1} π).obj G) q) :=
    fun hf q => (Equiv.finite_iff (e q)).mpr (h.finite_of_isProper inferInstance q)
  refine ⟨
    { vanishing := fun q hq => (e q).subsingleton_congr.mpr (h'.vanishing q hq)
      vanishing_of_isAffine := fun hY q hq =>
        (e q).subsingleton_congr.mpr (h'.vanishing_of_isAffine (isAffine_of_isAffineHom π) q hq)
      vanishing_of_isPrimePowerTorsion := fun p hp' hp0 hF q hq =>
        (e q).subsingleton_congr.mpr
          (h'.vanishing_of_isPrimePowerTorsion p hp' hp0 (hp p hF) q hq)
      finite_of_isPrimeToCharacteristicTorsion := fun _ htF q => hfin₁ htF q
      finite_of_isProper := fun hf _ q => hfin₂ hf q
      bijective_of_isPrimeToCharacteristicTorsion := fun htF k' _ _ _ _ q => by
        let : HasExt.{u + 1}
            (Sheaf (scalarExtension k k' (π ≫ fY)).smallEtaleTopology AddCommGrpCat.{u + 1}) :=
          hasExt_of_enoughInjectives.{u + 1} _
        exact (TorsionCurveAssertions.bijective_scalarExtension_directImage_iff fY π G k' q).2
          (h'.bijective_of_isPrimeToCharacteristicTorsion (ht htF) k' q)
      bijective_of_isProper := fun hf k' _ _ _ _ q => by
        let : HasExt.{u + 1}
            (Sheaf (scalarExtension k k' (π ≫ fY)).smallEtaleTopology AddCommGrpCat.{u + 1}) :=
          hasExt_of_enoughInjectives.{u + 1} _
        exact (TorsionCurveAssertions.bijective_scalarExtension_directImage_iff fY π G k' q).2
          (h'.bijective_of_isProper inferInstance k' q)
      surjective_restriction := fun U _ => by
        let : HasExt.{u + 1}
            (Sheaf ((π ⁻¹ᵁ U : X.Opens) : Scheme.{u}).smallEtaleTopology AddCommGrpCat.{u + 1}) :=
          hasExt_of_enoughInjectives.{u + 1} _
        have sq := (isPullback_morphismRestrict π U).flip
        have : IsFinite (π ∣_ U) := MorphismProperty.of_isPullback sq inferInstance
        have := isIso_etaleAbelianBaseChange_of_isFinite_of_isPullback_succUniverse π U.ι
          (π ⁻¹ᵁ U).ι (π ∣_ U) sq
        exact (surjective_restriction_directImage_iff π U.ι (π ⁻¹ᵁ U).ι (π ∣_ U) sq.w G 2).2
          (h'.surjective_restriction (π ⁻¹ᵁ U)) }, hfin₁, hfin₂⟩

end StrongTorsionCurveAssertions

end Stacks.EtaleCohomology

end
