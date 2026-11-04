module

public import StacksFrontier.AlgebraicGeometry.AmpleNoetherianDimensionOne.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleFiniteSurjective.Basic

/-!
# Ample invertible sheaves on proper schemes of dimension at most one

Let `R` be a Noetherian ring and let `X` be a scheme proper over `Spec R` whose underlying space
has dimension at most one. Then `X` carries an ample invertible `𝒪_X`-module.

This is the input "`X₁` is H-projective over `κ`; let `ℒ₁` be an ample invertible sheaf on
`X₁`" of the proof of [Stacks, Tag 0E7R], which the source obtains from [Stacks, Tag 0A26].

The argument is that of [Stacks, Tag 09NZ] with its last step replaced. The reduction
`Z = X_red` is Noetherian, separated, reduced and of dimension at most one, so it carries an ample
invertible module `M` ([Stacks, Tag 09NX]); the closed immersion `Z ⟶ X` has Noetherian target of
dimension at most one, so `M ≅ i^* L` for an invertible `L` on `X` ([Stacks, Tag 09NY]). Because
`X` is proper over a Noetherian ring and `Z ⟶ X` is finite and surjective, ampleness of `i^* L`
gives ampleness of `L` by [Stacks, Tag 0B5V]; this is where properness is used, and it replaces
the cohomological lift of [Stacks, Tag 09MS] that the general 09NZ needs.

## Main results

* `Stacks.FormalCurve.exists_isAmple_of_isProper_of_topologicalKrullDim_le_one`.
* `Stacks.FormalCurve.exists_invertibleTower` — an invertible module on the bottom of a tower of
  closed immersions `X₀ ⟶ X₁ ⟶ ⋯` of schemes with Noetherian underlying spaces of dimension at
  most one extends to a compatible system `(ℒₙ, θₙ : iₙ^* ℒₙ₊₁ ≅ ℒₙ)`. This is the source's
  "`ℒ₁` lifts to a compatible system `{ℒₙ}` of invertible sheaves on `{Xₙ}`", obtained by
  applying [Stacks, Tag 09NY] at each step.

## References

* [Stacks Project, Tag 0E7R](https://stacks.math.columbia.edu/tag/0E7R)
* [Stacks Project, Tag 0A26](https://stacks.math.columbia.edu/tag/0A26)
* [Stacks Project, Tag 09NZ](https://stacks.math.columbia.edu/tag/09NZ)
* [Stacks Project, Tag 0B5V](https://stacks.math.columbia.edu/tag/0B5V)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open RingedSpaceModuleAdjunction
open AlgebraicGeometry.Scheme.IdealSheafData (vanishingIdeal isReduced_subscheme_vanishingIdeal)

universe u

namespace Stacks.FormalCurve

/-- **An ample invertible module on a proper scheme of dimension at most one.** If `X` is proper
over `Spec R` for a Noetherian ring `R` and the underlying space of `X` has Krull dimension at
most one, then `X` carries an ample invertible `𝒪_X`-module. -/
theorem exists_isAmple_of_isProper_of_topologicalKrullDim_le_one {X : Scheme.{u}}
    {R : Type u} [CommRing R] [IsNoetherianRing R] (p : X ⟶ Spec (.of R)) [IsProper p]
    (hdim : topologicalKrullDim (X : Type u) ≤ 1) :
    ∃ (L : X.Modules) (_ : Stacks.Ample.IsInvertibleModule X L), Stacks.Ample.IsAmple X L := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have : AlgebraicGeometry.IsNoetherian X := ⟨⟩
  have : X.IsSeparated := ⟨by
    have : IsSeparated (p ≫ Limits.terminal.from _) := inferInstance
    rwa [Limits.terminal.comp_from] at this⟩
  set i := (vanishingIdeal (⊤ : Closeds X)).subschemeι with hi
  have : AlgebraicGeometry.IsNoetherian (vanishingIdeal (⊤ : Closeds X)).subscheme :=
    StacksTag09NX.isNoetherian_subscheme _
  have : AlgebraicGeometry.IsReduced (vanishingIdeal (⊤ : Closeds X)).subscheme :=
    isReduced_subscheme_vanishingIdeal _
  have : (vanishingIdeal (⊤ : Closeds X)).subscheme.IsSeparated :=
    StacksTag09NX.isSeparated_of_isClosedImmersion i
  have hdimZ : topologicalKrullDim ((vanishingIdeal (⊤ : Closeds X)).subscheme : Type u) ≤ 1 :=
    (StacksTag09NX.topologicalKrullDim_le_of_isClosedImmersion i).trans hdim
  obtain ⟨M, hM, hampleM⟩ :=
    Stacks.AmpleReducedDimensionOne.exists_isAmple_of_isReduced_of_topologicalKrullDim_le_one
      (vanishingIdeal (⊤ : Closeds X)).subscheme hdimZ
  have _ := hM
  have : NoetherianSpace (X : Type u) := AlgebraicGeometry.IsNoetherian.noetherianSpace
  obtain ⟨L, hL, ⟨e⟩⟩ :=
    Stacks.LiftInvertible.exists_modulePullback_iso_of_isClosedImmersion_of_dimension_le_one
      X (vanishingIdeal (⊤ : Closeds X)).subscheme i hdim M
  have _ := hL
  have hLinv : Stacks.Ample.IsInvertibleModule X L := hL
  have : AlgebraicGeometry.Surjective i :=
    Stacks.AmpleNoetherianDimensionOne.surjective_reductionι X
  have : Stacks.Ample.IsInvertibleModule (vanishingIdeal (⊤ : Closeds X)).subscheme
      ((modulePullback i.toLRSHom.toShHom).obj L) :=
    AlgebraicGeometry.SheafOfModules.isInvertible_pullback i L
  have hZ : Stacks.Ample.IsAmple (vanishingIdeal (⊤ : Closeds X)).subscheme
      ((modulePullback i.toLRSHom.toShHom).obj L) :=
    (Stacks.AmpleBridge.isAmple_iff_isAmple _ _).mpr
      (AlgebraicGeometry.Scheme.Modules.isAmple_of_iso e.symm hampleM)
  exact ⟨L, hLinv,
    Stacks.AmpleFiniteSurjective.isAmple_of_isAmple_modulePullback i L R p hZ⟩

/-- **The invertible module at the bottom of a tower extends up the tower.** Let
`i n : Xₙ ⟶ Xₙ₊₁` be closed immersions of schemes whose underlying spaces are Noetherian of
dimension at most one, and let `ℒ₀` be invertible on `X₀`. Then there are invertible modules
`ℒₙ` on every `Xₙ`, with `ℒ 0 = ℒ₀`, and isomorphisms `θₙ : iₙ^* ℒₙ₊₁ ≅ ℒₙ`.

Each step is [Stacks, Tag 09NY] for `iₙ`; the modules are built by recursion on `n`. -/
theorem exists_invertibleTower {Xn : ℕ → Scheme.{u}} (i : ∀ n, Xn n ⟶ Xn (n + 1))
    [∀ n, IsClosedImmersion (i n)] [∀ n, NoetherianSpace (Xn n)]
    (hdim : ∀ n, topologicalKrullDim (Xn n : Type u) ≤ 1)
    (L₀ : (Xn 0).Modules) [Stacks.Ample.IsInvertibleModule (Xn 0) L₀] :
    ∃ (L : ∀ n, (Xn n).Modules) (_hL : ∀ n, Stacks.Ample.IsInvertibleModule (Xn n) (L n)),
      L 0 = L₀ ∧ Nonempty (∀ n, (Scheme.Modules.pullback (i n)).obj (L (n + 1)) ≅ L n) := by
  have step : ∀ (n : ℕ) (M : {M : (Xn n).Modules // Stacks.Ample.IsInvertibleModule (Xn n) M}),
      ∃ M' : {M : (Xn (n + 1)).Modules // Stacks.Ample.IsInvertibleModule (Xn (n + 1)) M},
        Nonempty ((Scheme.Modules.pullback (i n)).obj M'.1 ≅ M.1) := by
    intro n M
    have := M.2
    obtain ⟨M', hM', ⟨e⟩⟩ :=
      Stacks.LiftInvertible.exists_modulePullback_iso_of_isClosedImmersion_of_dimension_le_one
        (Xn (n + 1)) (Xn n) (i n) (hdim (n + 1)) M.1
    exact ⟨⟨M', hM'⟩, ⟨e⟩⟩
  choose g hg using step
  let T : ∀ n, {M : (Xn n).Modules // Stacks.Ample.IsInvertibleModule (Xn n) M} :=
    fun n => Nat.rec (motive := fun m =>
      {M : (Xn m).Modules // Stacks.Ample.IsInvertibleModule (Xn m) M}) ⟨L₀, inferInstance⟩
      (fun m Tm => g m Tm) n
  exact ⟨fun n => (T n).1, fun n => (T n).2, rfl, ⟨fun n => (hg n (T n)).some⟩⟩

end Stacks.FormalCurve

end
