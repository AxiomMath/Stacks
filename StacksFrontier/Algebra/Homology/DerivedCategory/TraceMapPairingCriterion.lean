module

public import StacksFrontier.Algebra.Homology.DerivedCategory.TraceMapYonedaProduct
public import StacksFrontier.Algebra.Homology.DerivedCategory.HomToInjectiveSingle
public import StacksFrontier.Algebra.Homology.DerivedCategory.ProjectiveCorepresents
public import StacksFrontier.CategoryTheory.Triangulated.HomologicalDualityPairing

/-!
# Bijectivity of a trace map from a perfect pairing

Let `Φ : C ⥤ C'` commute with the shifts, `t : Φ(B) ⟶ L[c₀]` a trace with trace map
`T(y) = t[m] ∘ Φ(y)` (`Stacks.RelativeDuality.traceMap`), and `u : E ⟶ Φ(B)` a morphism (for
`Φ = Rf_*` and `B = Λ_X`, the unit `Λ_S ⟶ Rf_* Λ_X`). Suppose, for `c₀ + m = c` and `c + n = 0`,

* (a) `w ↦ Φ(w) ∘ u` is a bijection `Hom(B, B[n]) → Hom(E, Φ(B)[n])` (the adjunction);
* (b) `φ ↦ (x ↦ φ[n] ∘ x)` is a bijection `Hom(Φ(B), L[c]) → Hom_ℤ(Hom(E, Φ(B)[n]), Hom(E, L))`
  (morphisms into `L[c]` are detected by the classes coming from `E`);
* (c) `y ↦ (w ↦ T(y ∘ w) ∘ u)` is a bijection `Hom(B, B[m]) → Hom_ℤ(Hom(B, B[n]), Hom(E, L))`
  (a perfect cup product pairing, Poincaré duality on a fibre).

Then `T` is bijective in degree `m` (`Stacks.RelativeDuality.bijective_traceMap_of_pairing`): by
`Stacks.RelativeDuality.traceMap_shiftedHom_comp_comp`, (c) is (b) composed with `T` and with the
transpose of (a).

Condition (b) holds in the derived category of an abelian category for `E = P[0]` and `L = I[0]`
with `P` projective and `I` injective, as soon as `Hom(M, I) → Hom_ℤ(Hom(P, M), Hom(P, I))`,
`ψ ↦ (x ↦ ψ ∘ x)`, is bijective for every object `M`
(`Stacks.RelativeDuality.bijective_shiftedHom_comp_of_projective_of_injective`): both sides are
read on cohomology (`DerivedCategory.bijective_homologyMap_comp_of_injective`,
`DerivedCategory.homologyFromSingleAddEquiv`). For sheaves of `ℤ/ℓ`-modules over a separably
closed field and `P = I = ℤ/ℓ` this is linear algebra.

This is the fibre case of relative Poincaré duality for a smooth projective curve, in the proof of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main results

* `Stacks.RelativeDuality.bijective_traceMap_of_pairing`.
* `Stacks.RelativeDuality.bijective_comp_of_projective_of_injective`.
* `Stacks.RelativeDuality.bijective_shiftedHom_comp_of_projective_of_injective`.
-/

@[expose] public noncomputable section

open CategoryTheory

attribute [-instance] CategoryTheory.catToReflQuiver

namespace Stacks.RelativeDuality

section Pairing

variable {C C' : Type*} [Category* C] [Category* C'] [Preadditive C] [Preadditive C']
  [HasShift C ℤ] [HasShift C' ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [∀ n : ℤ, (shiftFunctor C' n).Additive]
  {Φ : C ⥤ C'} [Φ.CommShift ℤ] [Φ.Additive] {B : C} {L : C'} {c₀ : ℤ}
  {t : ShiftedHom (Φ.obj B) L c₀}

/-- The map `w ↦ Φ(w) ∘ u`, `Hom(B, B[n]) → Hom(E, Φ(B)[n])`. -/
def unitClassMap {E : C'} (u : E ⟶ Φ.obj B) (n : ℤ) :
    ShiftedHom B B n →+ ShiftedHom E (Φ.obj B) n :=
  AddMonoidHom.mk' (fun w => (ShiftedHom.mk₀ (0 : ℤ) rfl u).comp (w.map Φ) (add_zero n))
    (fun w₁ w₂ => by rw [ShiftedHom.map_add, ShiftedHom.comp_add])

/-- The map `φ ↦ (x ↦ φ[n] ∘ x)`, `Hom(Y, L[c]) → Hom_ℤ(Hom(E, Y[n]), Hom(E, L))`, `c + n = 0`. -/
def compPairing {D : Type*} [Category* D] [Preadditive D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive] (E Y L : D) {c n : ℤ} (hn : c + n = 0) :
    ShiftedHom Y L c →+ (ShiftedHom E Y n →+ ShiftedHom E L (0 : ℤ)) :=
  AddMonoidHom.mk' (fun φ => AddMonoidHom.mk' (fun x => x.comp φ hn)
      (fun x₁ x₂ => by rw [ShiftedHom.add_comp]))
    (fun φ₁ φ₂ => AddMonoidHom.ext fun x => ShiftedHom.comp_add _ _ _ _)

variable (t) in
/-- The trace pairing `y ↦ (w ↦ T(y ∘ w) ∘ u)`, `Hom(B, B[m]) → Hom_ℤ(Hom(B, B[n]), Hom(E, L))`,
for `c₀ + m + n = 0`. -/
def tracePairing {E : C'} (u : E ⟶ Φ.obj B) {m n : ℤ} (h : c₀ + (m + n) = 0) :
    ShiftedHom B B m →+ (ShiftedHom B B n →+ ShiftedHom E L (0 : ℤ)) :=
  AddMonoidHom.mk' (fun y => AddMonoidHom.mk' (fun w => (ShiftedHom.mk₀ (0 : ℤ) rfl u).comp
      (traceMap Φ t B (m + n) 0 h (w.comp y rfl)) (add_zero 0))
      (fun w₁ w₂ => by rw [ShiftedHom.add_comp, map_add, ShiftedHom.comp_add]))
    (fun y₁ y₂ => by
      ext w
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply]
      rw [ShiftedHom.comp_add, map_add, ShiftedHom.comp_add])

/-- **The trace map is bijective in degree `m` when the trace pairing is perfect**, granted the
adjunction (a) and the detection of morphisms into `L[c]` by classes from `E` (b). -/
theorem bijective_traceMap_of_pairing {E : C'} (u : E ⟶ Φ.obj B) {m n c : ℤ}
    (h : c₀ + m = c) (hn : c + n = 0)
    (ha : Function.Bijective (unitClassMap u n))
    (hb : Function.Bijective (compPairing E (Φ.obj B) L hn))
    (hc : Function.Bijective (tracePairing t u (by omega : c₀ + (m + n) = 0))) :
    Function.Bijective (traceMap Φ t B m c h) := by
  let β := AddEquiv.addMonoidHomCongrLeftEquiv (N := ShiftedHom E L (0 : ℤ))
    (AddEquiv.ofBijective _ ha).symm
  have hcomp : (β ∘ compPairing E (Φ.obj B) L hn) ∘ traceMap Φ t B m c h =
      tracePairing t u (by omega : c₀ + (m + n) = 0) := by
    funext y
    ext w
    exact traceMap_shiftedHom_comp_comp (ShiftedHom.mk₀ (0 : ℤ) rfl u) w rfl h
      (by omega) hn (add_zero n) (by omega) (add_zero 0) y
  rw [← hcomp] at hc
  exact (Function.Bijective.of_comp_iff' (β.bijective.comp hb) _).1 hc

end Pairing

section Detection

/-- The map `ψ ↦ (x ↦ ψ ∘ x)`, `Hom(M, I) → Hom_ℤ(Hom(P, M), Hom(P, I))`. -/
def homCompPairing {D : Type*} [Category* D] [Preadditive D] (P I M : D) :
    (M ⟶ I) → ((P ⟶ M) →+ (P ⟶ I)) :=
  fun ψ => AddMonoidHom.mk' (fun x => x ≫ ψ) (fun _ _ => Preadditive.add_comp _ _ _ _ _ _)

/-- Postcomposition with an isomorphism, as an additive equivalence. -/
private def postcompAddEquiv {D : Type*} [Category* D] [Preadditive D] (X : D) {Y Z : D}
    (e : Y ≅ Z) : (X ⟶ Y) ≃+ (X ⟶ Z) where
  toFun z := z ≫ e.hom
  invFun z := z ≫ e.inv
  left_inv z := by simp
  right_inv z := by simp
  map_add' z₁ z₂ := Preadditive.add_comp _ _ _ _ _ _

variable {𝒜 : Type*} [Category* 𝒜] [Abelian 𝒜] [HasDerivedCategory 𝒜] (P I : 𝒜) [Projective P]
  [Injective I]

/-- **Morphisms of `D(𝒜)` into `I[0]` are detected by the classes from `P[0]`**, for `P` projective
and `I` injective with `Hom(M, I) = Hom_ℤ(Hom(P, M), Hom(P, I))` for every `M`: the map
`ψ ↦ (x ↦ ψ ∘ x)`, `Hom(Y, I[0]) → Hom_ℤ(Hom(P[0], Y), Hom(P[0], I[0]))`, is bijective. -/
theorem bijective_comp_of_projective_of_injective
    (hα : ∀ M : 𝒜, Function.Bijective (homCompPairing P I M)) (Y : DerivedCategory 𝒜) :
    Function.Bijective (homCompPairing ((DerivedCategory.singleFunctor 𝒜 0).obj P)
      ((DerivedCategory.singleFunctor 𝒜 0).obj I) Y) := by
  let H := DerivedCategory.homologyFunctor 𝒜 0
  let σ := DerivedCategory.singleFunctorCompHomologyFunctorIso 𝒜 0
  -- `Hom(Y, I[0]) ≅ Hom(H⁰ Y, I)`
  let a : (Y ⟶ (DerivedCategory.singleFunctor 𝒜 0).obj I) → (H.obj Y ⟶ I) :=
    fun ψ => H.map ψ ≫ σ.hom.app I
  -- `Hom(P[0], Y) ≅ Hom(P, H⁰ Y)` and `Hom(P[0], I[0]) ≅ Hom(P, I)`
  let eY := DerivedCategory.homologyFromSingleAddEquiv P Y 0
  let κ : ((DerivedCategory.singleFunctor 𝒜 0).obj P ⟶ (DerivedCategory.singleFunctor 𝒜 0).obj I)
      ≃+ (P ⟶ I) :=
    (DerivedCategory.homologyFromSingleAddEquiv P
      ((DerivedCategory.singleFunctor 𝒜 0).obj I) 0).trans (postcompAddEquiv P (σ.app I))
  have hκ : ∀ z, κ z = σ.inv.app P ≫ H.map z ≫ σ.hom.app I := fun z => by
    show DerivedCategory.homologyFromSingleAddEquiv P _ 0 z ≫ σ.hom.app I = _
    rw [DerivedCategory.homologyFromSingleAddEquiv_apply, Category.assoc]
  rw [← Function.Bijective.of_comp_iff' (AddEquiv.addMonoidHomCongrRightEquiv κ).bijective]
  refine (Stacks.HomologicalDuality.bijective_iff_of_comp _ (homCompPairing P I (H.obj Y)) a
    (DerivedCategory.bijective_homologyMap_comp_of_injective Y I 0)
    eY.toAddMonoidHom eY.bijective (fun ψ x => ?_)).2 (hα (H.obj Y))
  show eY x ≫ (H.map ψ ≫ σ.hom.app I) = κ (x ≫ ψ)
  rw [hκ, DerivedCategory.homologyFromSingleAddEquiv_apply, H.map_comp]
  simp only [Category.assoc]
  rfl

/-- **Shifted morphisms of `D(𝒜)` into `I[0]` are detected by the classes from `P[0]`**: for `P`
projective and `I` injective with `Hom(M, I) = Hom_ℤ(Hom(P, M), Hom(P, I))` for every `M`, and
`c + n = 0`, the map `φ ↦ (x ↦ φ[n] ∘ x)`,
`Hom(Y, I[0][c]) → Hom_ℤ(Hom(P[0], Y[n]), Hom(P[0], I[0]))`, is bijective. -/
theorem bijective_shiftedHom_comp_of_projective_of_injective
    (hα : ∀ M : 𝒜, Function.Bijective (homCompPairing P I M)) (Y : DerivedCategory 𝒜) {c n : ℤ}
    (hn : c + n = 0) :
    Function.Bijective (compPairing ((DerivedCategory.singleFunctor 𝒜 0).obj P) Y
      ((DerivedCategory.singleFunctor 𝒜 0).obj I) hn) := by
  let P₀ := (DerivedCategory.singleFunctor 𝒜 0).obj P
  let I₀ := (DerivedCategory.singleFunctor 𝒜 0).obj I
  let e : (I₀⟦c⟧)⟦n⟧ ≅ I₀ :=
    (shiftFunctorAdd' (DerivedCategory 𝒜) c n 0 hn).symm.app I₀ ≪≫
      (shiftFunctorZero (DerivedCategory 𝒜) ℤ).app I₀
  let s : ShiftedHom Y I₀ c → (Y⟦n⟧ ⟶ I₀) := fun φ => φ⟦n⟧' ≫ e.hom
  have hs : Function.Bijective s :=
    (postcompAddEquiv (Y⟦n⟧) e).bijective.comp ⟨(shiftFunctor (DerivedCategory 𝒜) n).map_injective,
      (shiftFunctor (DerivedCategory 𝒜) n).map_surjective⟩
  let ζ : (P₀ ⟶ I₀⟦(0 : ℤ)⟧) ≃+ (P₀ ⟶ I₀) :=
    postcompAddEquiv P₀ ((shiftFunctorZero (DerivedCategory 𝒜) ℤ).app I₀)
  rw [← Function.Bijective.of_comp_iff' (AddEquiv.addMonoidHomCongrRightEquiv ζ).bijective]
  refine (Stacks.HomologicalDuality.bijective_iff_of_comp _ (homCompPairing P₀ I₀ (Y⟦n⟧)) s hs
    (AddMonoidHom.id _) Function.bijective_id (fun φ x => ?_)).2
      (bijective_comp_of_projective_of_injective P I hα (Y⟦n⟧))
  show x ≫ φ⟦n⟧' ≫ e.hom = ζ (ShiftedHom.comp (show ShiftedHom P₀ Y n from x) φ hn)
  simp [ζ, e, ShiftedHom.comp, postcompAddEquiv]

end Detection

end Stacks.RelativeDuality

end
