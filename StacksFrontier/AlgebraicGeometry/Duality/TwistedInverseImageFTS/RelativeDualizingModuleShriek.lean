module

public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.NewShriekRelativeDualizingModuleData
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekRelativeDualizingModule
public import StacksFrontier.AlgebraicGeometry.Duality.NormalizedOnOpens

/-!
# `H⁰(f^!𝒪)` and `H⁰(f_new^!𝒪)` are the relative dualizing module

This file assembles the two assertions of [Stacks, Tag 0BUL] into one statement.

* For a quasi-finite morphism `f : Y ⟶ X` of schemes separated and of finite type over a
  Noetherian scheme `S` and `f^!` the upper shriek of [Stacks, Tag 0A9Y] (at any
  compactification), the sheaf `H⁰(f^!𝒪_X)` carries the chart data of the relative dualizing
  module of [Stacks, Tag 0BVG]: on affine opens `Spec(B) = V ⊆ Y`, `Spec(A) = U ⊆ X` with
  `f(V) ⊆ U` its sections are identified with `ω_{B/A}`, compatibly with restriction; and these
  identifications define the canonical isomorphism with any relative dualizing module `ω_{Y/X}`.
* For a quasi-finite morphism `f` of schemes of finite type over a Noetherian base carrying a
  dualizing complex `ω_S^•`, not necessarily separated, and `f_new^!` built from the dualizing
  complexes normalized relative to `ω_S^•`, the sheaf `H⁰(f_new^!𝒪_X)` carries the same chart
  data, i.e. it is `ω_{Y/X}`.

## Main results

* `Stacks.Duality.relativeDualizingModule_upperShriek_structureSheaf`

## References

* [Stacks Project, Tag 0BUL](https://stacks.math.columbia.edu/tag/0BUL)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Duality

open Stacks.Discriminant

/-- **Stacks Project, Tag 0BUL.** (1) Let `S` be Noetherian, `f : X ⟶ Y` a locally quasi-finite
morphism of schemes separated and of finite type over `S` and `j` any compactification computing
`f^!` (Tag 0A9Y). Then `H⁰(f^!𝒪_Y)` is the sheaf of a relative dualizing module datum of `f`
(Tag 0BVG): its sections over affine opens `V ⊆ f⁻¹U` are identified with `ω_{Γ(V)/Γ(U)}`,
compatibly with restriction; and for every relative dualizing module `ω_{X/Y}` there is exactly
one family of isomorphisms on sections, compatible with restriction, carrying these affine
identifications to those of `ω_{X/Y}` — the canonical isomorphism `H⁰(f^!𝒪_Y) = ω_{X/Y}`.
(2) Let `S` be a Noetherian scheme with a dualizing complex `ω_S^•`, `f : X ⟶ Y` a locally
quasi-finite morphism of schemes of finite type over `S` (not necessarily separated), `ω_X^•`,
`ω_Y^•` dualizing complexes normalized relative to `ω_S^•` and `f_new^! = D_X ∘ Lf^* ∘ D_Y`.
Then `H⁰(f_new^!𝒪_Y)` is the sheaf of a relative dualizing module datum of `f`, i.e.
`H⁰(f_new^!𝒪_Y) = ω_{X/Y}`. -/
@[stacks 0BUL "the whole lemma: H^0(V, f^! O) = omega_{B/A} compatibly with restriction, the \
  canonical isomorphism H^0(f^! O) = omega_{Y/X}, and H^0(f_new^! O) = omega_{Y/X}"]
theorem relativeDualizingModule_upperShriek_structureSheaf :
    (∀ {S : Scheme.{u}} [IsNoetherian S] {X Y : FTS S} (f : X ⟶ Y) [LocallyQuasiFinite f.left]
        (j : CompactificationOf (Over.mk f.left)),
        (∃ D : RelativeDualizingModuleData f.left, D.sheaf = upperShriekStructureSheafZeroth f j) ∧
        ∀ ω : RelativeDualizingModuleData f.left,
          ∃! E : ∀ W : X.left.Opens,
              Γ(upperShriekStructureSheafZeroth f j, W) ≃ₗ[Γ(X.left, W)] Γ(ω.sheaf, W),
            (∀ (W W' : X.left.Opens) (h : W' ≤ W) (s : Γ(upperShriekStructureSheafZeroth f j, W)),
                E W' (Stacks.AlgebraicGeometry.QuasicoherentBaseChange.restrictₗ _ h s) =
                  Stacks.AlgebraicGeometry.QuasicoherentBaseChange.restrictₗ ω.sheaf h (E W s)) ∧
              ∀ (U : Y.left.affineOpens) (V : X.left.affineOpens) (hVU : V.1 ≤ f.left ⁻¹ᵁ U.1),
                letI : Algebra Γ(Y.left, U.1) Γ(X.left, V.1) := (f.left.appLE U V hVU).hom.toAlgebra
                ∀ (F : FiniteOpenFactorization.{u, u, u} Γ(Y.left, U.1) Γ(X.left, V.1))
                  (s : Γ(upperShriekStructureSheafZeroth f j, V.1)),
                  ω.localEquiv U V hVU F (E V.1 s) =
                    (upperShriekRelativeDualizingModuleData f j).localEquiv U V hVU F s) ∧
    (∀ (c : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), IsShriekable f → CompactificationOf (Over.mk f))
        {X Y S : Scheme.{u}} (f : X ⟶ Y) {q : Y ⟶ S} {p : X ⟶ S}
        {hp : IsFiniteTypeOverNoetherian p} {hq : IsFiniteTypeOverNoetherian q}
        {ωS : quasiCoherentDerivedCategoryPlusOfModel S}
        (𝒦X : NormalizedOnOpens (UpperShriek.ofCompactifications c) hp ωS)
        (𝒦Y : NormalizedOnOpens (UpperShriek.ofCompactifications c) hq ωS)
        (_hpe : f ≫ q = p) (_hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj)
        [LocallyQuasiFinite f],
        haveI := hp.source_noetherian
        haveI := hq.source_noetherian
        ∃ D : RelativeDualizingModuleData f,
          D.sheaf = NormalizedOnOpens.newShriekStructureSheafZeroth c f 𝒦X 𝒦Y) := by
  refine ⟨fun f _ j => ⟨⟨upperShriekRelativeDualizingModuleData f j, rfl⟩,
    existsUnique_upperShriekRelativeDualizingComparison f j⟩, ?_⟩
  intro c X Y S f q p hp hq ωS 𝒦X 𝒦Y hpe hωS _
  exact ⟨NormalizedOnOpens.newShriekRelativeDualizingModuleData c 𝒦X 𝒦Y hpe hωS, rfl⟩

end Stacks.Duality

end
