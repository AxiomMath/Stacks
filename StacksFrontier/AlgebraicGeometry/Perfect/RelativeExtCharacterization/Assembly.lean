module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeExtCharacterization.StageIdentification
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeExtCanonical.HocolimUnit

/-!
# The unit out of the homotopy colimit, for [Stacks, Tag 0DJV]

The stagewise units of `StageIdentification` are compatible with the transition maps of the
systems `Kₙ` and `L(Kₙ)` of [Stacks, Tag 0DJU], so they extend to a single morphism
`η : K ⟶ E ⊗^L Lf^*L` out of the homotopy colimits, and composing with `η` identifies
`Hom(L, N)` with `Hom(K, E ⊗^L Lf^*N)` on bounded below objects, by the truncation argument of the
proof of [Stacks, Tag 08IF] (B).

## Main results

* `exists_unit_bijective`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated CategoryTheory.Triangulated
  Opposite
open MonoidalCategory AlgebraicGeometry

universe u

attribute [local implicit_reducible] TopCat.Sheaf structureSheafRing CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

namespace Stacks.AlgebraicGeometry.RelativeExtCharacterization

open Stacks.SheafOfModules Stacks.AlgebraicGeometry.RelativeDerivedHomDual
open Stacks.Cohomology.RelativeExtCanonical

attribute [local instance] derivedMonoidalStructure derivedSymmetricStructure

/-- The canonical t-structure on `D(𝒪_Z)` at the standard model. -/
abbrev tStd (Z : Scheme.{u}) : TStructure (DStd Z) :=
  @DerivedCategory.TStructure.t (StructureSheafModules Z.sheaf) _ _ (HasDerivedCategory.standard _)

variable {X S : Scheme.{u}} (f : X ⟶ S) (E : DStd X)

/-- The stagewise units are compatible with the transition maps of the system
`n ↦ L(Kₙ)` of [Stacks, Tag 0DJU]. -/
theorem stageUnit_comp_transition (FK : ℕ ⥤ DStd X) (hFK : ∀ n, IsPerfectSite (FK.obj n))
    (hM : ∀ n, IsPerfectSite (stageM f E (FK.obj n))) (n : ℕ) :
    FK.map (homOfLE (Nat.le_succ n)) ≫ stageUnit f E (FK.obj (n + 1)) (hFK (n + 1)) (hM (n + 1)) =
      stageUnit f E (FK.obj n) (hFK n) (hM n) ≫
        (tensorPull f E).map ((dualSystem (pushforwardSheafHomSystem f FK E)).map
          (homOfLE (Nat.le_succ n))) :=
  stageUnit_comp f E _ (hFK n) (hFK (n + 1)) (hM n) (hM (n + 1))

/-- **The unit out of the homotopy colimit.** Let `K = hocolim Kₙ` with every `Kₙ` perfect and
every `Rf_*R𝓗om(Kₙ, E)` perfect, and `L = hocolim (Rf_*R𝓗om(Kₙ, E))^∨`, the system of
[Stacks, Tag 0DJU]. Suppose the coprojections of both systems are isomorphisms on `τ_{≥ k}`
from some stage on, for every `k`, that `E ⊗^L Lf^*(-)` shifts lower bounds by a fixed `a`, and
that the projection formula map is invertible at `(R𝓗om(Kₙ, E), N)` for every `N` in a class `P`
of bounded below objects. Then a single morphism `η : K ⟶ E ⊗^L Lf^*L` induces bijections
`Hom(L, N) ≃ Hom(K, E ⊗^L Lf^*N)` for every `N ∈ P`. -/
theorem exists_unit_bijective (FK : ℕ ⥤ DStd X) [HasCoproduct FK.obj] {K : DStd X}
    {c : ∀ n, FK.obj n ⟶ K} (hK : IsHomotopyColimitWith FK K c)
    (hFK : ∀ n, IsPerfectSite (FK.obj n)) (hM : ∀ n, IsPerfectSite (stageM f E (FK.obj n)))
    [HasCoproduct (dualSystem (pushforwardSheafHomSystem f FK E)).obj] {L : DStd S}
    {d : ∀ n, (dualSystem (pushforwardSheafHomSystem f FK E)).obj n ⟶ L}
    (hL : IsHomotopyColimitWith (dualSystem (pushforwardSheafHomSystem f FK E)) L d)
    (hstage : ∀ k : ℤ, ∃ n, IsIso (((tStd X).truncGE k).map (c n)) ∧
      IsIso (((tStd S).truncGE k).map (d n)))
    (a : ℤ) (hΦ : ∀ (N : DStd S) (m : ℤ), (tStd S).IsGE N m →
      (tStd X).IsGE ((tensorPull f E).obj N) (m + a))
    (P : ObjectProperty (DStd S)) (hPge : ∀ N, P N → ∃ m : ℤ, (tStd S).IsGE N m)
    (hpf : ∀ n N, P N → IsIso (pfMap f (rhom (FK.obj n) E) N)) :
    ∃ η : K ⟶ (tensorPull f E).obj L, ∀ N, P N →
      Function.Bijective (fun ψ : L ⟶ N ↦ η ≫ (tensorPull f E).map ψ) := by
  obtain ⟨η, hη⟩ := exists_unit_of_isHomotopyColimitWith (tensorPull f E) hK hL
    (fun n ↦ stageUnit f E (FK.obj n) (hFK n) (hM n))
    (stageUnit_comp_transition f E FK hFK hM)
  refine ⟨η, fun N hN ↦ ?_⟩
  obtain ⟨m, hm⟩ := hPge N hN
  exact @bijective_unit_comp_map _ _ _ (HasDerivedCategory.standard _) _ _ _
    (HasDerivedCategory.standard _) (tensorPull f E) a hΦ _ _ _ _ _ _ _ η hη P
    (fun n N hN ↦ bijective_stageUnit_comp f E _ (hFK n) (hM n) N (hpf n N hN)) hstage N hN m hm

end Stacks.AlgebraicGeometry.RelativeExtCharacterization
