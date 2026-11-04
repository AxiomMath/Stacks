module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexGeneratorCriterion

/-!
# The diagonal condition through the adjunct of `ξ`

Let `W` be a diagonal open of `f : X ⟶ S` with diagonal `Δ : X ⟶ W`, `K` an object of `D(𝒪_X)`
and `ζ : Δ_*𝒪_X ⟶ L pr₁^*K|_W`. Under the adjunction `Δ_* ⊣ R ℰom(𝒪_X, -)` of Stacks 0A76, `ζ` is
a map `𝒪_X[0] ⟶ R ℰom(𝒪_X, L pr₁^*K|_W)`, its adjunct
(`AlgebraicGeometry.Scheme.Hom.DiagonalOpen.diagonalAdjunct`).

## Main results

* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.diagonalAdjunct_diagonalGenerator`: the adjunct of
  the generator attached to an isomorphism `e : R ℰom(𝒪_X, L pr₁^*K|_W) ≅ 𝒪_X[0]` is `e⁻¹`.
* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.isIso_diagonalAction_of_isIso_diagonalAdjunct`: if
  the adjunct of `ζ` is an isomorphism, then `ζ` satisfies the diagonal condition of Stacks 0E2T.
* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.exists_iso_comp_diagonalGenerator`: a map `ξ`
  satisfying the diagonal condition is, up to an automorphism of `Δ_*𝒪_X`, the generator attached
  to some isomorphism `R ℰom(𝒪_X, L pr₁^*K|_W) ≅ 𝒪_X[0]`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf

/-- The adjunct of `δ⁻¹ ≫ δ ≫ x^♭` is `x`, with every object a variable. -/
theorem _root_.CategoryTheory.Adjunction.homEquiv_inv_hom_symm_apply {C D : Type*} [Category C]
    [Category D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) {A : C} {B P : D} (δ : P ≅ F.obj A)
    (x : A ⟶ G.obj B) : adj.homEquiv A B (δ.inv ≫ δ.hom ≫ (adj.homEquiv A B).symm x) = x := by
  rw [Iso.inv_hom_id_assoc, Equiv.apply_symm_apply]

/-- `δ ≫ (δ⁻¹ ≫ ζ)^♭♭ = ζ`, with every object a variable. -/
theorem _root_.CategoryTheory.Adjunction.hom_homEquiv_symm_homEquiv {C D : Type*} [Category C]
    [Category D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) {A : C} {B P : D} (δ : P ≅ F.obj A)
    (ζ : P ⟶ B) : δ.hom ≫ (adj.homEquiv A B).symm (adj.homEquiv A B (δ.inv ≫ ζ)) = ζ := by
  rw [Equiv.symm_apply_apply, Iso.hom_inv_id_assoc]

/-- Multiplication by `b`, an automorphism when `a * b = 1`, in a linear category. -/
def _root_.CategoryTheory.Linear.smulIsoOfMulEqOne {R C : Type*} [CommRing R] [Category C]
    [Preadditive C] [Linear R C] (A : C) (a b : R) (h : a * b = 1) : A ≅ A where
  hom := b • 𝟙 A
  inv := a • 𝟙 A
  hom_inv_id := by rw [Linear.smul_comp, Category.id_comp, smul_smul, mul_comm, h, one_smul]
  inv_hom_id := by rw [Linear.smul_comp, Category.id_comp, smul_smul, h, one_smul]

/-- `smulIsoOfMulEqOne A a b h` followed by `x` is `b • x`. -/
theorem _root_.CategoryTheory.Linear.smulIsoOfMulEqOne_hom_comp {R C : Type*} [CommRing R]
    [Category C] [Preadditive C] [Linear R C] {A B : C} (a b : R) (h : a * b = 1) (x : A ⟶ B) :
    (Linear.smulIsoOfMulEqOne A a b h).hom ≫ x = b • x := by
  change (b • 𝟙 A) ≫ x = b • x
  rw [Linear.smul_comp, Category.id_comp]

namespace AlgebraicGeometry.Scheme.Hom.DiagonalOpen

variable {X S : Scheme.{u}} {f : X ⟶ S} (D : DiagonalOpen f)

/-- The standard model of `D(𝒪_X)`. -/
local notation "Dˢ(" X ")" => @DerivedCategory (Scheme.Modules X) _ _
  (HasDerivedCategory.standard (Scheme.Modules X))

/-- **The adjunct of `ζ : Δ_*𝒪_X ⟶ L pr₁^*K|_W`**, the map
`𝒪_X[0] ⟶ R ℰom(𝒪_X, L pr₁^*K|_W)` it corresponds to under `Δ_* ⊣ R ℰom(𝒪_X, -)`
(Stacks 0A76). -/
def diagonalAdjunct (K : Dˢ(X))
    (ζ : D.diagonalObject ⟶ D.derivedPullbackProj K) :
    structureSingle X ⟶ D.diagonalExactSupport K :=
  (D.diagQuotient.derivedModulePushforwardSheafHomExactSupportAdjunction.homEquiv _ _)
    (D.diagonalObjectIso.inv ≫ ζ)

/-- The adjunct of the generator attached to `e` is `e⁻¹`. -/
theorem diagonalAdjunct_diagonalGenerator (K : Dˢ(X))
    (e : D.diagonalExactSupport K ≅ structureSingle X) :
    D.diagonalAdjunct K (D.diagonalGenerator K e) = e.inv := by
  unfold diagonalAdjunct diagonalGenerator
  exact Adjunction.homEquiv_inv_hom_symm_apply _ _ _

/-- The adjunct of the generator attached to `e` is invertible. -/
theorem isIso_diagonalAdjunct_diagonalGenerator (K : Dˢ(X))
    (e : D.diagonalExactSupport K ≅ structureSingle X) :
    IsIso (D.diagonalAdjunct K (D.diagonalGenerator K e)) := by
  rw [D.diagonalAdjunct_diagonalGenerator]
  infer_instance

/-- A map whose adjunct is invertible is the generator attached to the inverse of its adjunct. -/
theorem diagonalGenerator_diagonalAdjunct (K : Dˢ(X))
    (ζ : D.diagonalObject ⟶ D.derivedPullbackProj K) [IsIso (D.diagonalAdjunct K ζ)] :
    D.diagonalGenerator K (asIso (D.diagonalAdjunct K ζ)).symm = ζ := by
  unfold diagonalGenerator
  exact Adjunction.hom_homEquiv_symm_homEquiv _ _ _

/-- **A map with invertible adjunct satisfies the diagonal condition** of Stacks 0E2T. -/
theorem isIso_diagonalAction_of_isIso_diagonalAdjunct (K : Dˢ(X))
    (ζ : D.diagonalObject ⟶ D.derivedPullbackProj K) (h : IsIso (D.diagonalAdjunct K ζ)) :
    IsIso (D.diagonalAction K ζ) := by
  let e := (asIso (D.diagonalAdjunct K ζ)).symm
  refine D.isIso_diagonalAction_of_isPostcompGenerator K ⟨e⟩ ζ fun ζ' ↦ ?_
  obtain ⟨x, hx⟩ := (D.diagonalGenerator_spec K e).1 ζ'
  exact ⟨x, D.diagonalGenerator_diagonalAdjunct K ζ ▸ hx.symm⟩

/-- **A map satisfying the diagonal condition is a generator up to an automorphism**: it is
`a ≫ diagonalGenerator e` for an automorphism `a` of `Δ_*𝒪_X` and an isomorphism
`e : R ℰom(𝒪_X, L pr₁^*K|_W) ≅ 𝒪_X[0]`. -/
theorem exists_iso_comp_diagonalGenerator (K : Dˢ(X))
    (ξ : D.diagonalObject ⟶ D.derivedPullbackProj K) (h : IsIso (D.diagonalAction K ξ)) :
    ∃ (e : D.diagonalExactSupport K ≅ structureSingle X)
      (a : D.diagonalObject ≅ D.diagonalObject), ξ = a.hom ≫ D.diagonalGenerator K e := by
  obtain ⟨e⟩ := D.nonempty_diagonalExactSupport_iso K ξ h
  let := D.proj.linearStructureSheafModules
  have hG : IsIso (D.diagonalAction K (D.diagonalGenerator K e)) :=
    D.isIso_diagonalAction_of_isIso_diagonalAdjunct K _
      (D.isIso_diagonalAdjunct_diagonalGenerator K e)
  obtain ⟨a, ha, -⟩ := D.existsUnique_eq_smul_of_isIso_diagonalAction h (D.diagonalGenerator K e)
  obtain ⟨b, hb, -⟩ := D.existsUnique_eq_smul_of_isIso_diagonalAction hG ξ
  obtain ⟨c, -, hc⟩ := D.existsUnique_eq_smul_of_isIso_diagonalAction hG
    (D.diagonalGenerator K e)
  have hab : a * b = 1 :=
    (hc (a * b) (by dsimp only; rw [mul_smul, ← hb, ← ha])).trans (hc 1 (one_smul _ _).symm).symm
  exact ⟨e, Linear.smulIsoOfMulEqOne _ a b hab,
    hb.trans (Linear.smulIsoOfMulEqOne_hom_comp a b hab _).symm⟩

end AlgebraicGeometry.Scheme.Hom.DiagonalOpen

end
