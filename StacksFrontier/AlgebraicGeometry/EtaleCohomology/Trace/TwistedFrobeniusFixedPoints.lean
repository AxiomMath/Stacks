module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.TwistedFrobeniusTwist
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.DimensionZeroTraceFormula

/-!
# Fixed points of a twisted Frobenius over a scheme without rational points

Let `f : V ⟶ U` be a morphism of schemes over a finite field `k` and `σ : V ⟶ V` a morphism over
`U`. If `U` has no `k`-rational point, then the twisted geometric Frobenius `φ = σ̄ ≫ π̄` of
`V_k̄` has no fixed `k̄`-point: the image in `U` of a fixed point is fixed by the arithmetic
Frobenius of `k̄`, hence comes from a rational point of `U`.

This is the last step of Step 9 of the proof of [Stacks, Tag 03UG]: `g⁻¹π_V` has no fixed point
on `V_k̄`, `f : V → U` being the Galois cover and `U(k) = ∅`.

## Main results

* `Stacks.EtaleCohomology.comp_geometricFrobenius_left_eq_specMap_comp`: on a `k̄`-point the
  geometric Frobenius is the arithmetic Frobenius of `k̄`.
* `Stacks.EtaleCohomology.not_comp_twistedGeometricFrobenius_eq`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

variable {k : Type u} [Field k] [Fintype k] (kbar : Type u) [Field kbar] [IsAlgClosed kbar]
  [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p] [CharP kbar p]
  (hcard : Fintype.card k = p ^ q)

/-- On a `k̄`-point of a scheme over `k`, the geometric Frobenius is the arithmetic Frobenius of
`k̄`: `a ≫ π_U = Spec(σ) ≫ a`. -/
lemma comp_geometricFrobenius_left_eq_specMap_comp (U : Over (Spec (.of k)))
    (a : Spec (.of kbar) ⟶ U.left) :
    a ≫ (geometricFrobenius U p q hcard).left =
      Spec.map (CommRingCat.ofHom (arithmeticFrobenius k kbar p q hcard).toAlgHom.toRingHom) ≫
        a := by
  have hk : IsInCharacteristic (Spec (.of kbar)) p := isInCharacteristic_specAlgebraMap k kbar p
  rw [geometricFrobenius_left_eq_absoluteFrobeniusPow, ← absoluteFrobeniusPow_naturality a p hk,
    specMap_eq_absoluteFrobeniusPow _ p q hk (fun z => by
      simp [arithmeticFrobenius, iterateFrobenius_def])]

/-- **A twisted Frobenius has no fixed point over a scheme without rational points.** Let
`f : V ⟶ U` be a morphism over `k`, `σ : V ⟶ V` a morphism with `σ ≫ f = f`, and suppose that
`U` has no `k`-rational point. Then no `k̄`-point `y` of `V_k̄` over `k̄` satisfies
`y ≫ σ̄ ≫ π̄ = y`. -/
theorem not_comp_twistedGeometricFrobenius_eq {V U : Over (Spec (.of k))} (f : V ⟶ U) (σ : V ⟶ V)
    (hσ : σ ≫ f = f) [IsEmpty (rationalPoints U.hom)]
    (y : Spec (.of kbar) ⟶ fieldBaseChange V kbar)
    (hy : y ≫ pullback.snd V.hom (specAlgebraMap k kbar) = 𝟙 _) :
    y ≫ twistedGeometricFrobenius V σ kbar p q hcard ≠ y := by
  intro hfix
  let a : Spec (.of kbar) ⟶ U.left := y ≫ fieldBaseChangeProj V kbar ≫ f.left
  have ha : a ≫ U.hom = specAlgebraMap k kbar := by
    simp only [a, Category.assoc, Over.w f]
    rw [show fieldBaseChangeProj V kbar ≫ V.hom =
        pullback.snd V.hom (specAlgebraMap k kbar) ≫ specAlgebraMap k kbar from pullback.condition,
      ← Category.assoc, hy, Category.id_comp]
  have hσf : σ.left ≫ f.left = f.left := congrArg CommaMorphism.left hσ
  have key : twistedGeometricFrobenius V σ kbar p q hcard ≫ fieldBaseChangeProj V kbar =
      fieldBaseChangeProj V kbar ≫ (geometricFrobenius V p q hcard).left ≫ σ.left := by
    rw [Category.assoc, geometricFrobeniusBaseChange_comp_fst, ← Category.assoc,
      fieldBaseChangeMap_comp_fst, Category.assoc, geometricFrobenius_left_comp p q hcard σ]
  have hfixa :
      Spec.map (CommRingCat.ofHom (arithmeticFrobenius k kbar p q hcard).toAlgHom.toRingHom) ≫
        a = a := by
    rw [← comp_geometricFrobenius_left_eq_specMap_comp kbar p q hcard U a]
    calc a ≫ (geometricFrobenius U p q hcard).left
        = y ≫ fieldBaseChangeProj V kbar ≫ (geometricFrobenius V p q hcard).left ≫ f.left := by
          simp only [a, Category.assoc, geometricFrobenius_left_comp p q hcard f]
      _ = y ≫ fieldBaseChangeProj V kbar ≫ (geometricFrobenius V p q hcard).left ≫ σ.left ≫
            f.left := by rw [hσf]
      _ = (y ≫ twistedGeometricFrobenius V σ kbar p q hcard) ≫ fieldBaseChangeProj V kbar ≫
            f.left := by
          rw [Category.assoc]
          congr 1
          rw [← Category.assoc (twistedGeometricFrobenius V σ kbar p q hcard), key]
          simp only [Category.assoc]
      _ = a := by rw [hfix]
  obtain ⟨x, hx, -⟩ := exists_rationalPoint_of_specMap_comp_eq kbar U.hom
    (arithmeticFrobenius k kbar p q hcard) (fun z => arithmeticFrobenius_apply k kbar p q hcard z)
    a ha hfixa
  exact IsEmpty.false (α := rationalPoints U.hom) ⟨x, hx⟩

end Stacks.EtaleCohomology
