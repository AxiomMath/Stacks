module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.BaseFieldExtension.Blowup
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.BaseFieldExtension.ChernCharacter
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.BaseFieldExtension.ChowBaseChange
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.BaseFieldExtension.GlobalSections
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.BaseFieldExtension.TraceDescent
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.WeilChernData

/-!
# Tag 0FVT: the axioms (A1)–(A9) descend along an extension of fields

Let `k'/k` be an extension of fields and `F'/F` an extension of fields of characteristic zero.
Let `F(1), H^*, c₁^H` be data (D0), (D1), (D2') for `k` and `F`, and `F'(1), (H')^*, c₁^{H'}`
data (D0), (D1), (D2') for `k'` and `F'`, together with an isomorphism `F(1) ⊗_F F' ≅ F'(1)` and
functorial isomorphisms `H^*(X) ⊗_F F' ≅ (H')^*(X_{k'})` compatible with the first Chern classes
(`Stacks.WeilCohomology.FieldExtensionComparison`). If the primed data satisfy (A1)–(A9), so do
the unprimed ones.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct Function Stacks.Chow

universe u w w'

namespace Stacks.WeilCohomology

open SmoothProjectiveScheme

namespace SmoothProjectiveScheme

variable {k : Type u} [Field k] {k' : Type u} [Field k'] [Algebra k k']

/-- The morphism `Spec k' ⟶ Spec k` of a field extension `k'/k` is surjective. -/
instance surjective_specMap : AlgebraicGeometry.Surjective (ArtinSchreier.specExt k k') :=
  ⟨fun _ => ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩⟩

/-- **Base change preserves nonempty equidimensional schemes.** -/
theorem isNonemptyEquidimensional_baseChange {X : (SmoothProjectiveScheme k).FullSubcategory}
    {d : ℕ} (hX : IsNonemptyEquidimensional X d) :
    IsNonemptyEquidimensional ((baseChange k k').obj X) d where
  nonempty := by
    obtain ⟨x⟩ := hX.nonempty
    obtain ⟨y, -⟩ := (pullback.fst X.obj.hom (ArtinSchreier.specExt k k')).surjective x
    exact ⟨y⟩
  relativeDimension := by
    have : LocallyOfFiniteType X.obj.hom := inferInstance
    exact relativeDimension_pullback_snd X.obj.hom (ArtinSchreier.specExt k k') d
      hX.relativeDimension

end SmoothProjectiveScheme

variable {k : Type u} [Field k] {k' : Type u} [Field k'] [Algebra k k']
  {F : Type w} [Field F] {F' : Type w'} [Field F'] [Algebra F F']

namespace FieldExtensionComparison

variable [CharZero F] [CharZero F'] {𝔇 : FirstChernClassData k F} (𝔚' : WeilChernData k' F')
  (Φ : FieldExtensionComparison 𝔇 𝔚'.toFirstChernClassData)

omit [CharZero F] in
include Φ in
/-- **Axiom (A1) descends**: `𝔇` satisfies the coproduct axiom. -/
theorem coproductAxiom' : 𝔇.CoproductAxiom := Φ.coproductAxiom 𝔚'.coproduct

omit [CharZero F] in
include Φ in
/-- **Axiom (A2) descends**: `𝔇` satisfies the pullback axiom. -/
theorem pullbackAxiom' : 𝔇.PullbackAxiom := Φ.pullbackAxiom 𝔚'.pullback

omit [CharZero F] in
include Φ in
/-- **Axiom (A3) descends**: `𝔇` satisfies the projective bundle axiom. -/
theorem projectiveBundleAxiom' : 𝔇.ProjectiveBundleAxiom :=
  Φ.projectiveBundleAxiom 𝔚'.pullback 𝔚'.projectiveBundle

omit [CharZero F] in
include Φ in
/-- **Axiom (A4) descends**: `𝔇` satisfies the divisor axiom. -/
theorem divisorAxiom' : 𝔇.DivisorAxiom := Φ.divisorAxiom 𝔚'.divisor

omit [CharZero F] in
include Φ in
/-- **Axiom (A5) descends**: `𝔇` satisfies the Künneth axiom. -/
theorem kunnethAxiom' : 𝔇.KunnethAxiom := Φ.kunnethAxiom 𝔚'.kunneth

/-- The cycle class map `γ` of the descended data. -/
abbrev γ (X : (SmoothProjectiveScheme k).FullSubcategory) (i : ℕ) :
    codimensionChowGroup k X.obj.hom i →+ tateTwist F 𝔇.tate (𝔇.H X) i :=
  𝔇.cycleClassOf (Φ.coproductAxiom' 𝔚') (Φ.pullbackAxiom' 𝔚') (Φ.projectiveBundleAxiom' 𝔚')
    (Φ.divisorAxiom' 𝔚') X i

/-- **`γ` commutes with base change** (the square of the proof of Tag 0FVT): the image of
`γ(α) ∈ H^{2i}(X)(i)` in `(H')^{2i}(X_{k'})(i)` is `γ'(g^*α)`. -/
theorem γ_codimensionChowBaseChange (X : (SmoothProjectiveScheme k).FullSubcategory) (i : ℕ)
    (a : codimensionChowGroup k X.obj.hom i) :
    𝔚'.γ ((baseChange k k').obj X) i (SmoothProjectiveScheme.codimensionChowBaseChange X i a) =
      Φ.twist X i (Φ.γ 𝔚' X i a) := by
  rw [WeilChernData.γ, FirstChernClassData.cycleClassOf, γ, FirstChernClassData.cycleClassOf,
    FirstChernClassData.IsCohomologicalChernCharacter.codimensionCycleClass_apply,
    FirstChernClassData.IsCohomologicalChernCharacter.codimensionCycleClass_apply]
  rw [← AlgEquiv.apply_symm_apply (rationalChernCharacterAlgEquiv _ _)
      (smoothChowEquiv _ (codimensionToRationalChow k' _ _ _)),
    SmoothProjectiveScheme.symm_rationalChernCharacterAlgEquiv_codimensionChowBaseChange,
    Φ.cycleClassMap_baseChange (Φ.coproductAxiom' 𝔚') (Φ.pullbackAxiom' 𝔚')
      (Φ.projectiveBundleAxiom' 𝔚') (Φ.divisorAxiom' 𝔚') 𝔚'.coproduct 𝔚'.pullback
      𝔚'.projectiveBundle 𝔚'.divisor, AlgEquiv.apply_symm_apply]

/-- **The classes of the diagonals correspond**: the image of `γ([Δ_X])` in
`(H')^*((X × X)_{k'})` is `u^d` times the pullback of `γ'([Δ_{X_{k'}}])` along
`(X × X)_{k'} ≅ X_{k'} × X_{k'}`, in the coordinates of the twists. -/
theorem pull_κ_γ_diagonalClass (X : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ)
    (hX : IsNonemptyEquidimensional X d) :
    𝔚'.pull (baseChangeProdIso X X).hom
        (𝔚'.κ _ d (𝔚'.γ (prod ((baseChange k k').obj X) ((baseChange k k').obj X)) d
          (diagonalClass ((baseChange k k').obj X) d))) =
      Φ.tateUnit ^ (d : ℤ) •
        Φ.ρ (prod X X) (𝔇.κ _ d (Φ.γ 𝔚' (prod X X) d (diagonalClass X d))) := by
  have h1 := 𝔚'.isCohomologicalChernCharacter.codimensionCycleClass_codimensionGysin
    (baseChangeProdIso X X).hom d (diagonalClass ((baseChange k k').obj X) d)
  rw [← SmoothProjectiveScheme.codimensionChowBaseChange_diagonalClass X d hX] at h1
  change 𝔚'.γ _ d _ = _ at h1
  rw [Φ.γ_codimensionChowBaseChange] at h1
  rw [← FirstChernClassData.κ_pullTw]
  change 𝔚'.κ _ d (𝔚'.pullTw (baseChangeProdIso X X).hom d (𝔚'.γ _ d _)) = _
  rw [← h1, κ_twist]

include Φ in
/-- **Axiom (A6) descends.** -/
theorem traceAxiom :
    𝔇.TraceAxiomFor (Φ.kunnethAxiom' 𝔚') (Φ.γ 𝔚') := by
  intro X d hX
  obtain ⟨lam', hlam'⟩ := 𝔚'.trace _ d (isNonemptyEquidimensional_baseChange (k' := k') hX)
  exact Φ.exists_traceContract_eq_one (Φ.kunnethAxiom' 𝔚') 𝔚'.kunneth X d _ _
    (Φ.pull_κ_γ_diagonalClass 𝔚' X d hX) lam' hlam'

include Φ in
/-- **Axiom (A9) descends.** -/
theorem divisorTraceAxiom (h9 : 𝔚'.DivisorTrace) :
    𝔇.DivisorTraceAxiomFor (Φ.kunnethAxiom' 𝔚') (Φ.γ 𝔚') := by
  intro X Y d hX hY i D hD e he lamX lamY hlX hlY a ha
  have hD' : Stacks.Divisors.IsEffectiveCartierDivisor (D.comap (baseChangeProj (k' := k') X)) :=
    Stacks.Divisors.isPullbackDefined_of_flat _ D hD
  have ext := fun Z d hZ => Φ.exists_traceContract_eq_one_extend (Φ.kunnethAxiom' 𝔚')
    𝔚'.kunneth Z d _ _ (Φ.pull_κ_γ_diagonalClass 𝔚' Z d hZ)
  obtain ⟨lamX', hlX', hrelX⟩ := ext X (d + 1) hX lamX hlX
  obtain ⟨lamY', hlY', hrelY⟩ := ext Y d hY lamY hlY
  have key := h9 _ _ d (isNonemptyEquidimensional_baseChange hX)
    (isNonemptyEquidimensional_baseChange hY) ((baseChange k k').map i) _ hD'
    (baseChangeSubschemeIso i D e he) (baseChangeSubschemeIso_hom_ι i D e he) lamX' lamY' hlX'
    hlY' (Φ.ρ X a) (Φ.ρ_mem_grade _ _ a ha)
  have hc : Φ.twistOne X (𝔇.c₁ X (picardClassOf _ (Stacks.Divisors.divisorSheaf D)
      (Stacks.Divisors.isInvertible_divisorSheaf D))) =
      𝔚'.c₁ _ (picardClassOf _ (Stacks.Divisors.divisorSheaf (D.comap (baseChangeProj X)))
        (Stacks.Divisors.isInvertible_divisorSheaf _)) :=
    (Φ.c₁_comm _ _ _).trans (congrArg _ (picardClassOf_eq_of_iso _ _ _ _ _
      (Stacks.Divisors.invertibleSheafPullbackIso (baseChangeProj X) D)))
  have hκ : 𝔚'.κ _ 1 (𝔚'.c₁ _ (picardClassOf _
      (Stacks.Divisors.divisorSheaf (D.comap (baseChangeProj X)))
        (Stacks.Divisors.isInvertible_divisorSheaf _))) =
      Φ.tateUnit • Φ.ρ X (𝔇.κ X 1 (𝔇.c₁ X (picardClassOf _ (Stacks.Divisors.divisorSheaf D)
        (Stacks.Divisors.isInvertible_divisorSheaf D)))) := by
    rw [← hc, κ_twistOne]
    rfl
  rw [← Φ.ρ_pull, hκ, mul_smul_comm, ← map_mul, map_smul, hrelX, hrelY, smul_eq_mul] at key
  have hu : Φ.tateUnit ≠ 0 := Φ.tateUnit_ne_zero
  rw [show (((d + 1 : ℕ) : ℤ)) = (d : ℤ) + 1 by push_cast; ring, zpow_add_one₀ hu] at key
  apply (algebraMap F F').injective
  have hud : Φ.tateUnit ^ (d : ℤ) ≠ 0 := zpow_ne_zero _ hu
  field_simp at key
  exact key

/-- **The data (D0), (D1), (D2') for `k` and `F` satisfy (A1)–(A7)** when the data for `k'`
and `F'` do (Tag 0FVT). -/
def toWeilChernData : WeilChernData k F where
  toFirstChernClassData := 𝔇
  coproduct := Φ.coproductAxiom' 𝔚'
  pullback := Φ.pullbackAxiom' 𝔚'
  projectiveBundle := Φ.projectiveBundleAxiom' 𝔚'
  divisor := Φ.divisorAxiom' 𝔚'
  kunneth := Φ.kunnethAxiom' 𝔚'
  trace := Φ.traceAxiom 𝔚'
  blowup := Φ.blowupAxiom 𝔚'.blowup

/-- The data (D0), (D1), (D2') underlying `Φ.toWeilChernData 𝔚'` are `𝔇`. -/
@[simp]
theorem toWeilChernData_toFirstChernClassData :
    (Φ.toWeilChernData 𝔚').toFirstChernClassData = 𝔇 :=
  rfl

/-- (A8) for the descended data. -/
theorem globalSections_toWeilChernData (h8 : 𝔚'.GlobalSections) :
    (Φ.toWeilChernData 𝔚').GlobalSections :=
  Φ.globalSectionsAxiom h8

/-- (A9) for the descended data. -/
theorem divisorTrace_toWeilChernData (h9 : 𝔚'.DivisorTrace) :
    (Φ.toWeilChernData 𝔚').DivisorTrace :=
  Φ.divisorTraceAxiom 𝔚' h9

end FieldExtensionComparison

/-- **Stacks Tag 0FVT.** Let `k'/k` be an extension of fields and `F'/F` an extension of fields
of characteristic zero. Let `𝔇 = (F(1), H^*, c₁^H)` be data (D0), (D1), (D2') for `k` and `F`
and `𝔚' = (F'(1), (H')^*, c₁^{H'})` data (D0), (D1), (D2') for `k'` and `F'`, given with an
isomorphism `F(1) ⊗_F F' ≅ F'(1)` and isomorphisms `H^*(X) ⊗_F F' ≅ (H')^*(X_{k'})` of graded
`F'`-algebras, functorial in the smooth projective scheme `X` over `k`, under which `c₁^H` and
`c₁^{H'}` correspond (`Φ`, a `Stacks.WeilCohomology.FieldExtensionComparison`). If
`F'(1), (H')^*, c₁^{H'}` satisfy (A1)–(A9) — (A1)–(A7) being the fields of
`Stacks.WeilCohomology.WeilChernData`, (A8) `GlobalSections`, (A9) `DivisorTrace` — then
`F(1), H^*, c₁^H` satisfy (A1)–(A9): (A1)–(A5), (A6) for the cycle class map `γ` of Tag 0FIF of
the data `𝔇` (which (A1)–(A4) determine), (A7), (A8), and (A9) for that `γ`. -/
@[stacks 0FVT]
theorem exists_axioms_of_fieldExtension [CharZero F] [CharZero F'] (𝔇 : FirstChernClassData k F)
    (𝔚' : WeilChernData k' F') (Φ : FieldExtensionComparison 𝔇 𝔚'.toFirstChernClassData)
    (h8 : 𝔚'.GlobalSections) (h9 : 𝔚'.DivisorTrace) :
    ∃ (hA1 : 𝔇.CoproductAxiom) (hA2 : 𝔇.PullbackAxiom) (hA3 : 𝔇.ProjectiveBundleAxiom)
      (hA4 : 𝔇.DivisorAxiom) (hA5 : 𝔇.KunnethAxiom),
      𝔇.TraceAxiomFor hA5 (𝔇.cycleClassOf hA1 hA2 hA3 hA4) ∧ 𝔇.BlowupAxiom ∧
        𝔇.GlobalSectionsAxiom ∧ 𝔇.DivisorTraceAxiomFor hA5 (𝔇.cycleClassOf hA1 hA2 hA3 hA4) :=
  ⟨Φ.coproductAxiom' 𝔚', Φ.pullbackAxiom' 𝔚', Φ.projectiveBundleAxiom' 𝔚', Φ.divisorAxiom' 𝔚',
    Φ.kunnethAxiom' 𝔚', Φ.traceAxiom 𝔚', Φ.blowupAxiom 𝔚'.blowup, Φ.globalSectionsAxiom h8,
    Φ.divisorTraceAxiom 𝔚' h9⟩

/-- **Tag 0FVT, bundled**: the data `𝔇` underlie data satisfying (A1)–(A7) which also satisfy
(A8) and (A9). -/
theorem exists_weilChernData_of_fieldExtension [CharZero F] [CharZero F']
    (𝔇 : FirstChernClassData k F) (𝔚' : WeilChernData k' F')
    (Φ : FieldExtensionComparison 𝔇 𝔚'.toFirstChernClassData) (h8 : 𝔚'.GlobalSections)
    (h9 : 𝔚'.DivisorTrace) :
    ∃ 𝔚 : WeilChernData k F, 𝔚.toFirstChernClassData = 𝔇 ∧ 𝔚.GlobalSections ∧ 𝔚.DivisorTrace :=
  ⟨Φ.toWeilChernData 𝔚', rfl, Φ.globalSections_toWeilChernData 𝔚' h8,
    Φ.divisorTrace_toWeilChernData 𝔚' h9⟩

end Stacks.WeilCohomology
