module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.BoundednessTorsion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyUnboundedExactness
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedBoundedCohomologicalDimension
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowNaturalTransformations
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
import StacksCore.Tactic.StacksAttribute

/-!
# Boundedness of `Rf_!` (Stacks 0G2A)

Let `f : X ⟶ Y` be a morphism of schemes with `Y` quasi-compact, `j : X ⟶ X̄` a compactification
of `X` over `Y` and `Λ` a ring. [Stacks, Tag 0G2A] asserts that there is an integer `N` such that
for `E ∈ D⁺_tors(X_étale, Λ)`, or `E ∈ D(X_étale, Λ)` when `Λ` is torsion,

1. `Hⁱ(Rf_!(τ_{≤ a} E)) → Hⁱ(Rf_! E)` is an isomorphism for `i ≤ a`,
2. `Hⁱ(Rf_! E) → Hⁱ(Rf_!(τ_{≥ b - N} E))` is an isomorphism for `i ≥ b`,
3. if `Hⁱ(E) = 0` for `i ∉ [a, b]` then `Hⁱ(Rf_! E) = 0` for `i ∉ [a, b + N]`.

The case of `D⁺_tors` is
`Stacks.EtaleCohomology.exists_isLE_derivedLowerShriek_of_isTorsionPlus` and
`Stacks.EtaleCohomology.exists_isIso_homology_derivedLowerShriek_map_truncGEπ_of_isTorsionPlus`.
This file treats the unbounded case for a torsion ring `Λ`, on
`Stacks.EtaleCohomology.derivedLowerShriekUnbounded`, and combines the two.

## Main results

* `Stacks.EtaleCohomology.computesRightDerived_singleFunctor_of_injective`: an injective object
  is right acyclic in the sense of Stacks 0157(3)/05SX.
* `Stacks.EtaleCohomology.bounds_derivedLowerShriekUnbounded`: part (3) on `D(X_étale, Λ)` for
  a torsion ring.
* `Stacks.EtaleCohomology.bounded_derivedLowerShriekUnbounded`: parts (1), (2) and (3) on
  `D(X_étale, Λ)` for a torsion ring.
* `Stacks.EtaleCohomology.exists_bounded_derivedLowerShriek`: **Stacks 0G2A**.

## Implementation notes

The proof follows [Stacks, Tag 0G2A]. `Rj_!` is extension by zero applied degreewise
(`Stacks.EtaleCohomology.etaleModuleDerivedExtensionByZeroUnboundedIso`), which is exact, so it
preserves the bounds. Every sheaf of `Λ`-modules is torsion, so by Stacks 0A3V and Stacks 095U
`R^q f̄_* = 0` for `q > 2d`; Stacks 07K7
(`CategoryTheory.Functor.hasRightDerivedFunctor_of_isZero_rightDerived`) then bounds the unbounded
`Rf̄_*`, which is a right derived functor along the homotopy category
(`Stacks.Injectives.KInjectiveResolution.isRightDerivedFunctor_homotopyCategoryUnit`). Parts (1)
and (2) follow from part (3) and the truncation triangles, `Rf_!` being triangulated.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Pretriangulated
open Stacks.Injectives.KInjectiveResolution

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.EtaleCohomology

section General

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] (F : C ⥤ D) [F.Additive] [EnoughInjectives C]

/-- **An injective object is right acyclic** in the sense of Stacks 0157(3) with 05SX: the complex
`I[0]` computes the right derived functor of `K⁺(C) ⥤ D⁺(D)`. Every bounded below complex has a
quasi-isomorphism to a bounded below complex of injectives, at which the unit of
`F.rightDerivedFunctorPlus` is invertible, so computing `RF` at `I[0]` is invertibility of the
unit there, which holds since `I[0]` is a complex of injectives. -/
theorem computesRightDerived_singleFunctor_of_injective (I : C) [Injective I] :
    (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).ComputesRightDerived
      (HomotopyCategory.Plus.quasiIso C) ((HomotopyCategory.Plus.singleFunctor C 0).obj I) := by
  have : ∀ m : ℤ, Injective (((HomotopyCategory.Plus.singleFunctor C 0).obj I).obj.as.X m) :=
    fun m ↦ inferInstanceAs
      (Injective (((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj I).X m))
  have : (HomotopyCategory.Plus.quasiIso C).HasLeftCalculusOfFractions := by
    rw [HomotopyCategory.Plus.quasiIso_eq_subcategoryAcyclic_trW]; infer_instance
  rw [Functor.computesRightDerived_iff_isIso_app _ DerivedCategory.Plus.Qh
    F.rightDerivedFunctorPlus (HomotopyCategory.Plus.quasiIso C) F.rightDerivedFunctorPlusUnit _
    (fun K => ?_)]
  · infer_instance
  · let r : (HomotopyCategory.Plus.localizerMorphism C).RightResolution K := Classical.arbitrary _
    exact ⟨_, r.w, r.hw, inferInstance⟩

end General

variable (Λ : Type) [Ring Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
  (j : CompactificationOf (Over.mk f))

/-- **Part (3) of Stacks 0G2A on the unbounded derived category, for a torsion ring.** If
`m • 1 = 0` in `Λ` with `m > 0` and `Y` is quasi-compact, there is `N` such that the unbounded
`Rf_!` preserves lower bounds and raises upper bounds by at most `N`. -/
theorem bounds_derivedLowerShriekUnbounded (m : ℕ) (hm : 0 < m) (hΛ : (m : Λ) = 0) (d : ℕ)
    (hd : ∀ y : Y, topologicalKrullDim (j.toBase.fiber y) ≤ d) :
    ∀ E : DerivedCategory (EtaleModules.{u, 0} Λ X),
      (∀ a : ℤ, E.IsGE a → ((derivedLowerShriekUnbounded.{u, 0} f j Λ).obj E).IsGE a) ∧
        ∀ b : ℤ, E.IsLE b →
          ((derivedLowerShriekUnbounded.{u, 0} f j Λ).obj E).IsLE (b + (2 * d : ℕ)) := by
  let F := etaleModuleDirectImage.{u, 0} Λ j.toBase
  let RF := etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ j.toBase
  let α := homotopyCategoryUnit F RF (etaleModuleDerivedDirectImageUnboundedUnit.{u, 0} Λ j.toBase)
  have h07K7 := Functor.hasRightDerivedFunctor_of_isZero_rightDerived F
    F.rightDerivedFunctorPlus F.rightDerivedFunctorPlusUnit
    (fun Z => (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).ComputesRightDerived
      (HomotopyCategory.Plus.quasiIso _) ((HomotopyCategory.Plus.singleFunctor _ 0).obj Z))
    (fun _ => Iff.rfl)
    (fun Z => ⟨Injective.under Z, Injective.ι Z, inferInstance,
      computesRightDerived_singleFunctor_of_injective F _⟩)
    (2 * d + 1) (fun Z => by
      have h := Stacks.BoundedCohomologicalDimension.isLE_rightDerivedFunctorPlus_single F Z
        (2 * d : ℕ) 0 (fun p hp => isZero_rightDerived_etaleModuleDirectImage_of_isProper Λ
          j.toBase d hd _ (torsionSheafProperty_etaleModuleForget_obj_of_nsmul_eq_zero Λ m hm hΛ _)
          p (by exact_mod_cast hp))
      exact DerivedCategory.isZero_of_isLE _ (0 + (2 * d : ℕ)) _ (by push_cast; omega))
  obtain ⟨-, -, hRF⟩ := h07K7
  obtain ⟨-, hE⟩ := hRF RF α
  let G := etaleModuleExtensionByZero.{u, 0} Λ j.immersion
  intro E
  let e := ((etaleModuleDerivedExtensionByZeroUnboundedIso.{u, 0} Λ j.immersion).app E).symm
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · have hGE : (G.mapDerivedCategory.obj E).IsGE a := by
      rw [DerivedCategory.isGE_iff]
      intro i hi
      exact (G.map_isZero (DerivedCategory.isZero_of_isGE E a i hi)).of_iso
        ((G.mapDerivedCategoryHomologyIso i).app E)
    exact (hE _).2.2.1 a (DerivedCategory.TStructure.t.isGE_of_iso e a)
  · have hLE : (G.mapDerivedCategory.obj E).IsLE b := by
      rw [DerivedCategory.isLE_iff]
      intro i hi
      exact (G.map_isZero (DerivedCategory.isZero_of_isLE E b i hi)).of_iso
        ((G.mapDerivedCategoryHomologyIso i).app E)
    have := (hE _).2.2.2 b (DerivedCategory.TStructure.t.isLE_of_iso e b)
    have heq : b + ((2 * d + 1 : ℕ) : ℤ) - 1 = b + ((2 * d : ℕ) : ℤ) := by push_cast; omega
    rwa [heq] at this

/-- **Parts (1), (2) and (3) of Stacks 0G2A on the unbounded derived category, for a torsion
ring**, with `N = 2d` for a bound `d` on the dimension of the fibres of `f̄`. Parts (1) and (2)
follow from part (3) and the truncation triangles: `Rf_!` is isomorphic to the triangulated
functor `j_! ⋙ Rf̄_*`. -/
theorem bounded_derivedLowerShriekUnbounded (m : ℕ) (hm : 0 < m) (hΛ : (m : Λ) = 0) (d : ℕ)
    (hd : ∀ y : Y, topologicalKrullDim (j.toBase.fiber y) ≤ d)
    (E : DerivedCategory (EtaleModules.{u, 0} Λ X)) :
    (∀ a i : ℤ, i ≤ a → IsIso ((DerivedCategory.homologyFunctor _ i).map
        ((derivedLowerShriekUnbounded.{u, 0} f j Λ).map
          ((DerivedCategory.TStructure.t.truncLEι a).app E)))) ∧
      (∀ b i : ℤ, b ≤ i → IsIso ((DerivedCategory.homologyFunctor _ i).map
        ((derivedLowerShriekUnbounded.{u, 0} f j Λ).map
          ((DerivedCategory.TStructure.t.truncGEπ (b - (2 * d : ℕ))).app E)))) ∧
      (∀ a : ℤ, E.IsGE a → ((derivedLowerShriekUnbounded.{u, 0} f j Λ).obj E).IsGE a) ∧
      ∀ b : ℤ, E.IsLE b →
        ((derivedLowerShriekUnbounded.{u, 0} f j Λ).obj E).IsLE (b + (2 * d : ℕ)) := by
  have hB := bounds_derivedLowerShriekUnbounded Λ f j m hm hΛ d hd
  let := etaleModuleDerivedDirectImageUnboundedCommShift.{u, 0} Λ j.toBase
  have := etaleModuleDerivedDirectImageUnbounded_isTriangulated.{u, 0} Λ j.toBase
  let G := (etaleModuleExtensionByZero.{u, 0} Λ j.immersion).mapDerivedCategory ⋙
    etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ j.toBase
  let e : derivedLowerShriekUnbounded.{u, 0} f j Λ ≅ G :=
    Functor.isoWhiskerRight (etaleModuleDerivedExtensionByZeroUnboundedIso.{u, 0} Λ j.immersion) _
  have hmap : ∀ {A B : DerivedCategory (EtaleModules.{u, 0} Λ X)} (g : A ⟶ B) (i : ℤ),
      IsIso ((DerivedCategory.homologyFunctor _ i).map (G.map g)) →
        IsIso ((DerivedCategory.homologyFunctor _ i).map
          ((derivedLowerShriekUnbounded.{u, 0} f j Λ).map g)) := by
    intro A B g i h
    have hg : (derivedLowerShriekUnbounded.{u, 0} f j Λ).map g =
        e.hom.app A ≫ G.map g ≫ e.inv.app B := by
      rw [← Category.assoc, ← e.hom.naturality, Category.assoc, Iso.hom_inv_id_app,
        Category.comp_id]
    rw [hg, Functor.map_comp, Functor.map_comp]
    infer_instance
  have hGE : ∀ (A : DerivedCategory (EtaleModules.{u, 0} Λ X)) (a : ℤ), A.IsGE a →
      (G.obj A).IsGE a := fun A a hA => by
    have := (hB A).1 a hA
    exact DerivedCategory.TStructure.t.isGE_of_iso (e.app A) a
  have hLE : ∀ (A : DerivedCategory (EtaleModules.{u, 0} Λ X)) (b : ℤ), A.IsLE b →
      (G.obj A).IsLE (b + (2 * d : ℕ)) := fun A b hA => by
    have := (hB A).2 b hA
    exact DerivedCategory.TStructure.t.isLE_of_iso (e.app A) _
  let t := DerivedCategory.TStructure.t (C := EtaleModules.{u, 0} Λ X)
  refine ⟨fun a i hi => hmap _ i ?_, fun b i hbi => hmap _ i ?_, (hB E).1, (hB E).2⟩
  · let T := (t.triangleLEGE a (a + 1) rfl).obj E
    have hT := t.triangleLEGE_distinguished a (a + 1) rfl E
    have h3 : (G.mapTriangle.obj T).obj₃.IsGE (a + 1) :=
      hGE ((t.truncGE (a + 1)).obj E) (a + 1) (t.isGE_truncGE_obj E (a + 1) (a + 1))
    exact DerivedCategory.isIso_homologyMap_mor₁_of_isGE₃ (G.mapTriangle.obj T)
      (G.map_distinguished T hT) i (a + 1) h3 (by omega)
  · let N : ℤ := (2 * d : ℕ)
    let T := (t.triangleLEGE (b - N - 1) (b - N) (by omega)).obj E
    have hT := t.triangleLEGE_distinguished (b - N - 1) (b - N) (by omega) E
    have h1 : (G.mapTriangle.obj T).obj₁.IsLE (b - 1) := by
      have := hLE ((t.truncLE (b - N - 1)).obj E) (b - N - 1)
        (t.isLE_truncLE_obj E (b - N - 1) (b - N - 1) le_rfl)
      have heq : b - N - 1 + (2 * d : ℕ) = b - 1 := by omega
      rwa [heq] at this
    exact DerivedCategory.isIso_homologyMap_mor₂_of_isLE₁ (G.mapTriangle.obj T)
      (G.map_distinguished T hT) i (b - 1) h1 (by omega)

/-- **[Stacks, Tag 0G2A].** Let `f : X ⟶ Y` be a morphism of schemes with `Y` quasi-compact,
`j` a compactification of `X` over `Y` (through which `Rf_! = Rf̄_* ∘ Rj_!` is defined), and `Λ`
a ring. There is an integer `N` such that for `E ∈ D⁺_tors(X_étale, Λ)`, and, when `Λ` is
torsion, for `E ∈ D(X_étale, Λ)`:

1. `Hⁱ(Rf_!(τ_{≤ a} E)) ⟶ Hⁱ(Rf_! E)` is an isomorphism for `i ≤ a`;
2. `Hⁱ(Rf_! E) ⟶ Hⁱ(Rf_!(τ_{≥ b - N} E))` is an isomorphism for `i ≥ b`;
3. if `Hⁱ(E) = 0` for `i ∉ [a, b]` then `Hⁱ(Rf_! E) = 0` for `i ∉ [a, b + N]`; stated as the two
   implications `E ≥ a ⇒ Rf_! E ≥ a` and `E ≤ b ⇒ Rf_! E ≤ b + N`, which together are part (3)
   for all `-∞ ≤ a ≤ b ≤ ∞`.

[Stacks, Tag 0G2A] assumes `f` separated of finite type and `X`, `Y` quasi-compact and
quasi-separated; here the compactification `j` is given, and only quasi-compactness of `Y` is
used. -/
@[stacks 0G2A "all three parts, for E in D+_tors(X, Lambda) (Rf_! = derivedLowerShriek on \
D+) and, when Lambda is torsion, for E in D(X, Lambda) (Rf_! = derivedLowerShriekUnbounded), \
with one N for both; part (3) is the conjunction of its lower and upper bound halves, which is \
the source's statement for all -infinity <= a <= b <= infinity"]
theorem exists_bounded_derivedLowerShriek [CompactSpace Y] :
    ∃ N : ℕ,
      (∀ E : DerivedCategory.Plus (EtaleModules.{u, 0} Λ X), isTorsionPlus.{u, 0} Λ X E →
        (∀ a i : ℤ, i ≤ a → IsIso ((DerivedCategory.Plus.homologyFunctor _ i).map
            ((derivedLowerShriek.{u, 0} f j Λ).map
              ((DerivedCategory.Plus.TStructure.t.truncLEι a).app E)))) ∧
          (∀ b i : ℤ, b ≤ i → IsIso ((DerivedCategory.Plus.homologyFunctor _ i).map
            ((derivedLowerShriek.{u, 0} f j Λ).map
              ((DerivedCategory.Plus.TStructure.t.truncGEπ (b - N)).app E)))) ∧
          (∀ a : ℤ, E.IsGE a → ((derivedLowerShriek.{u, 0} f j Λ).obj E).IsGE a) ∧
          ∀ b : ℤ, E.IsLE b →
            (DerivedCategory.Plus.ι.obj ((derivedLowerShriek.{u, 0} f j Λ).obj E)).IsLE
              (b + N)) ∧
      ((∃ m : ℕ, 0 < m ∧ (m : Λ) = 0) → ∀ E : DerivedCategory (EtaleModules.{u, 0} Λ X),
        (∀ a i : ℤ, i ≤ a → IsIso ((DerivedCategory.homologyFunctor _ i).map
            ((derivedLowerShriekUnbounded.{u, 0} f j Λ).map
              ((DerivedCategory.TStructure.t.truncLEι a).app E)))) ∧
          (∀ b i : ℤ, b ≤ i → IsIso ((DerivedCategory.homologyFunctor _ i).map
            ((derivedLowerShriekUnbounded.{u, 0} f j Λ).map
              ((DerivedCategory.TStructure.t.truncGEπ (b - N)).app E)))) ∧
          (∀ a : ℤ, E.IsGE a → ((derivedLowerShriekUnbounded.{u, 0} f j Λ).obj E).IsGE a) ∧
          ∀ b : ℤ, E.IsLE b →
            ((derivedLowerShriekUnbounded.{u, 0} f j Λ).obj E).IsLE (b + N)) := by
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_fiber_le j.toBase
  refine ⟨2 * d, fun E hE =>
    ⟨fun a i hi => isIso_homology_derivedLowerShriek_map_truncLEι Λ f j E a i hi,
    fun b i hbi =>
      isIso_homology_derivedLowerShriek_map_truncGEπ_of_isTorsionPlus Λ f j d hd E hE b i hbi,
    fun a ha => isGE_derivedLowerShriek_obj Λ f j E a,
    fun b hb => isLE_derivedLowerShriek_of_isTorsionPlus Λ f j d hd E hE b hb⟩,
    fun ⟨m, hm, hΛ⟩ E => bounded_derivedLowerShriekUnbounded Λ f j m hm hΛ d hd E⟩

end Stacks.EtaleCohomology

end
