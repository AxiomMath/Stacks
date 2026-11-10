module

public import StacksFrontier.AlgebraicGeometry.Different.DualizingModulesQuasi.BaseChange
public import StacksFrontier.AlgebraicGeometry.Different.NoetherDifferent.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Different.NoetherDifferent.Pairing
public import StacksFrontier.AlgebraicGeometry.Discriminant.NoetherPairingNaturality

/-!
# Flat base change of the Noether pairing

The canonical pairing between the relative dualizing module of a finite-open factorization and
the diagonal annihilator commutes with flat base change: pairing the base-changed dualizing
module against the base-changed annihilator gives the scalar extension of the original pairing.

## Main definitions

* `Stacks.Discriminant.diagonalAnnihilatorFlatBaseChange` is the map on diagonal annihilators
  induced by flat base change, obtained by restricting the canonical map of enveloping algebras.

## Main results

* `Stacks.Discriminant.noetherPairing_baseChange`: the base-change square for the canonical
  pairing commutes.

## Implementation notes

The base-changed algebra is written `A₁ ⊗[A] B` rather than `B ⊗[A] A₁`. The finite-open
factorization is kept explicit, as it is in the construction of the dualizing module, of its
base-change map and of the pairing. The source's Noetherian and quasi-finite hypotheses are
replaced by the factorization together with the finite-type hypothesis that base change of the
diagonal annihilator needs.

The base-changed intermediate algebra is spelled `A₁ ⊗[A] F.middle` rather than
`(F.baseChange A₁).middle`, with the two instances it carries supplied explicitly from
`Stacks.Discriminant.FiniteOpenFactorization.baseChangeAlgebra` and
`Stacks.Discriminant.FiniteOpenFactorization.baseChange_scalarTower`. The two spellings agree by
definition, but only the first is a tensor product syntactically, which is what the rewrites on
pure tensors need.

## References

* [Stacks Project, Tag 0BVR](https://stacks.math.columbia.edu/tag/0BVR)
-/

@[expose] public section

open scoped TensorProduct

namespace Stacks.Discriminant

universe u v w x

/-- Contracting a base-changed functional against the base change of an element of the
enveloping algebra is the scalar extension of the contraction before base change. -/
private theorem tensorContract_envelopingBaseChange
    (A : Type u) (C : Type v) (A₁ : Type x)
    [CommRing A] [CommRing C] [CommRing A₁]
    [Algebra A C] [Algebra A A₁]
    (f : Module.Dual A C) (z : C ⊗[A] C) :
    tensorContract A₁ (A₁ ⊗[A] C) (f.baseChange A₁) (envelopingBaseChange A C A₁ z) =
      Algebra.TensorProduct.includeRight (tensorContract A C f z) := by
  induction z using TensorProduct.inductionOn with
  | tmul c d =>
      rw [envelopingBaseChange_tmul]
      simp [tensorContract, Module.Dual.baseChange_apply_tmul,
        Algebra.TensorProduct.includeRight_apply]
  | add z₁ z₂ hz₁ hz₂ => simp only [map_add, hz₁, hz₂]

/-- The canonical map of enveloping algebras is natural in the algebra: pushing an element of
the enveloping algebra of `C/A` forward to `B/A` and then base changing to `A₁` agrees with base
changing first and pushing forward along the scalar extension of `C → B`. The hypothesis is that
the scalar extension of `C → B` is computed on pure tensors in the expected way. -/
private lemma envelopingBaseChange_naturality (A : Type u) (C : Type v) (B : Type w)
    (A₁ : Type x) [CommRing A] [CommRing C] [CommRing B] [CommRing A₁]
    [Algebra A C] [Algebra C B] [Algebra A B] [IsScalarTower A C B] [Algebra A A₁]
    [Algebra (A₁ ⊗[A] C) (A₁ ⊗[A] B)] [IsScalarTower A₁ (A₁ ⊗[A] C) (A₁ ⊗[A] B)]
    (hcompat : ∀ c : C, algebraMap (A₁ ⊗[A] C) (A₁ ⊗[A] B) ((1 : A₁) ⊗ₜ[A] c) =
      (1 : A₁) ⊗ₜ[A] algebraMap C B c)
    (z : C ⊗[A] C) :
    envelopingBaseChange A B A₁
        (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A C B)
          (IsScalarTower.toAlgHom A C B) z) =
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom A₁ (A₁ ⊗[A] C) (A₁ ⊗[A] B))
        (IsScalarTower.toAlgHom A₁ (A₁ ⊗[A] C) (A₁ ⊗[A] B))
        (envelopingBaseChange A C A₁ z) := by
  induction z using TensorProduct.inductionOn with
  | tmul c d =>
      rw [Algebra.TensorProduct.map_tmul, envelopingBaseChange_tmul,
        envelopingBaseChange_tmul, Algebra.TensorProduct.map_tmul]
      simp only [IsScalarTower.coe_toAlgHom', hcompat]
  | add z₁ z₂ h₁ h₂ => simp [h₁, h₂]

/-- The canonical map on annihilators of the diagonal after flat base change. -/
def diagonalAnnihilatorFlatBaseChange
    (A : Type u) (B : Type v) (A₁ : Type x)
    [CommRing A] [CommRing B] [CommRing A₁]
    [Algebra A B] [Algebra A A₁]
    [Algebra.FiniteType A B] [Module.Flat A A₁] :
    (diagonalAnnihilator A B) → (diagonalAnnihilator A₁ (A₁ ⊗[A] B)) :=
  fun j ↦ ⟨envelopingBaseChange A B A₁ j.1, by
    rw [← map_diagonalAnnihilator_eq A B A₁]
    exact Ideal.mem_map_of_mem _ j.2⟩

/-- **Stacks Project, Tag 0BVR (flat base change).** The canonical pairing
between the relative dualizing module and the diagonal annihilator commutes
with flat base change. -/
@[stacks 0BVR "flat_base_change"]
theorem noetherPairing_baseChange
    {A : Type u} {B : Type v} (A₁ : Type x)
    [CommRing A] [CommRing B] [CommRing A₁]
    [Algebra A B] [Algebra A A₁]
    [Algebra.FiniteType A B] [Module.Flat A A₁]
    (F : FiniteOpenFactorization.{u, v, w} A B)
    (ω : dualizingModule F)
    (j : diagonalAnnihilator A B) :
    letI : Algebra B (A₁ ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
    noetherPairing (FiniteOpenFactorization.baseChange F A₁)
        (dualizingModule.baseChange F A₁ ω)
        (diagonalAnnihilatorFlatBaseChange A B A₁ j) =
      algebraMap B (A₁ ⊗[A] B) (noetherPairing F ω j) := by
  classical
  let : Algebra B (A₁ ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  let : Algebra (A₁ ⊗[A] F.middle) (A₁ ⊗[A] B) :=
    FiniteOpenFactorization.baseChangeAlgebra F A₁
  let : IsScalarTower A₁ (A₁ ⊗[A] F.middle) (A₁ ⊗[A] B) :=
    FiniteOpenFactorization.baseChange_scalarTower F A₁
  set F₁ := FiniteOpenFactorization.baseChange F A₁ with hF₁
  have hRange := range_diagonalAnnihilatorBaseChange A F.middle B
    (specMap_ulift_isOpenImmersion (algebraMap F.middle B)
      F.isOpenEmbedding_comap F.awayMap_bijective)
  let φ := diagonalAnnihilatorBaseChange A F.middle B
  let φJ : B ⊗[F.middle] (↑(diagonalAnnihilator A F.middle)) →ₗ[B]
      (↑(diagonalAnnihilator A B)) :=
    φ.codRestrict ((diagonalAnnihilator A B).restrictScalars B) (by
      intro z
      change φ z ∈ (diagonalAnnihilator A B).restrictScalars B
      rw [← hRange]
      exact ⟨z, rfl⟩)
  have hφJ : Function.Surjective φJ := by
    intro j₀
    obtain ⟨z, hz⟩ := (show j₀.1 ∈ LinearMap.range φ from hRange ▸ j₀.2)
    exact ⟨z, Subtype.ext hz⟩
  have hcompat (c : F.middle) :
      algebraMap (A₁ ⊗[A] F.middle) (A₁ ⊗[A] B) ((1 : A₁) ⊗ₜ[A] c) =
        (1 : A₁) ⊗ₜ[A] algebraMap F.middle B c := by
    change Algebra.TensorProduct.map (AlgHom.id A A₁)
        (IsScalarTower.toAlgHom A F.middle B) ((1 : A₁) ⊗ₜ[A] c) = _
    simp [Algebra.TensorProduct.map_tmul]
  have hdiag (x y : diagonalAnnihilator A B) :
      diagonalAnnihilatorFlatBaseChange A B A₁ (x + y) =
        diagonalAnnihilatorFlatBaseChange A B A₁ x +
          diagonalAnnihilatorFlatBaseChange A B A₁ y :=
    Subtype.ext (by simp [diagonalAnnihilatorFlatBaseChange])
  have hinc (x : B) : (1 : A₁) ⊗ₜ[A] x = algebraMap B (A₁ ⊗[A] B) x := rfl
  induction ω using dualizingModule.induction_on with
  | tmul f b =>
      obtain ⟨z, rfl⟩ := hφJ j
      have hGen (z : B ⊗[F.middle] (↑(diagonalAnnihilator A F.middle))) :
          noetherPairing F₁
              (dualizingModule.baseChange F A₁ (dualizingModule.tmul F f b))
              (diagonalAnnihilatorFlatBaseChange A B A₁ (φJ z)) =
            algebraMap B (A₁ ⊗[A] B)
              (noetherPairing F (dualizingModule.tmul F f b) (φJ z)) := by
        induction z using TensorProduct.inductionOn with
        | tmul y jc =>
            let jc₁ := diagonalAnnihilatorFlatBaseChange A F.middle A₁ jc
            let jb := φJ (y ⊗ₜ[F.middle] jc)
            let jb₁ := diagonalAnnihilatorFlatBaseChange A B A₁ jb
            have hjb₁ : jb₁.1 =
                diagonalAnnihilatorBaseChange A₁ (A₁ ⊗[A] F.middle) (A₁ ⊗[A] B)
                  (((1 : A₁) ⊗ₜ[A] y) ⊗ₜ[A₁ ⊗[A] F.middle] jc₁) := by
              change envelopingBaseChange A B A₁
                  (diagonalAnnihilatorBaseChange A F.middle B (y ⊗ₜ[F.middle] jc)) = _
              rw [diagonalAnnihilatorBaseChange_tmul_eq, map_mul,
                envelopingBaseChange_naturality A F.middle B A₁ hcompat,
                diagonalAnnihilatorBaseChange_tmul_eq, envelopingBaseChange_tmul]
              simp [jc₁, diagonalAnnihilatorFlatBaseChange,
                ← Algebra.TensorProduct.one_def]
            have hsrc : noetherPairing F (dualizingModule.tmul F f b) jb =
                b * y * algebraMap F.middle B (tensorContract A F.middle f jc.1) := by
              apply noetherPairing_apply_of_eq_baseChange F f b y jc jb
              rfl
            have hcontract' :
                tensorContract A₁ (A₁ ⊗[A] F.middle) (f.baseChange A₁) jc₁.1 =
                  Algebra.TensorProduct.includeRight
                    (tensorContract A F.middle f jc.1) :=
              tensorContract_envelopingBaseChange A F.middle A₁ f jc.1
            have htarget := noetherPairing_apply_of_eq_baseChange F₁
              (f.baseChange A₁) ((1 : A₁) ⊗ₜ[A] b) ((1 : A₁) ⊗ₜ[A] y) jc₁ jb₁ hjb₁
            calc
              noetherPairing F₁
                  (dualizingModule.baseChange F A₁ (dualizingModule.tmul F f b)) jb₁ =
                  noetherPairing F₁
                    (dualizingModule.tmul F₁ (f.baseChange A₁) ((1 : A₁) ⊗ₜ[A] b)) jb₁ := by
                      rw [dualizingModule.baseChange_tmul]
              _ = ((1 : A₁) ⊗ₜ[A] b) * ((1 : A₁) ⊗ₜ[A] y) *
                    algebraMap (A₁ ⊗[A] F.middle) (A₁ ⊗[A] B)
                      (tensorContract A₁ (A₁ ⊗[A] F.middle) (f.baseChange A₁) jc₁.1) := htarget
              _ = algebraMap B (A₁ ⊗[A] B)
                    (noetherPairing F (dualizingModule.tmul F f b) jb) := by
                      rw [hcontract', hsrc, Algebra.TensorProduct.includeRight_apply, hcompat,
                        hinc b, hinc y,
                        hinc (algebraMap F.middle B (tensorContract A F.middle f jc.1))]
                      simp only [map_mul]
        | add z₁ z₂ h₁ h₂ =>
            simp only [map_add, hdiag, h₁, h₂]
      exact hGen z
  | add ω₁ ω₂ h₁ h₂ =>
      rw [map_add (dualizingModule.baseChange F A₁) ω₁ ω₂]
      simp only [map_add, LinearMap.add_apply, h₁, h₂]

end Stacks.Discriminant
