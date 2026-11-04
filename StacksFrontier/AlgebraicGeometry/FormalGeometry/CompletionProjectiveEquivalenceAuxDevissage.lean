module

public import StacksFrontier.AlgebraicGeometry.AmpleCohomologicalCriterion.Twist
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProjectiveEquivalenceAuxVanishing
public import StacksFrontier.AlgebraicGeometry.HighTwistDevissage.Cohomology
public import StacksFrontier.AlgebraicGeometry.LerayAffineBase.Basic

/-!
# The descending induction behind part (2) of [Stacks, Tag 0897], uniform in the grading

`StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionProjectiveEquivalenceAuxVanishing.lean`
supplies the two ends of the descending induction on the cohomological degree that proves part
(2) of [Stacks, Tag 0897] for the associated graded algebra of an ideal sheaf: a degree `e`
above which every twist of every homogeneous piece is acyclic, and Serre vanishing for finitely
many degrees at once. This file supplies the induction itself.

The point of difficulty, and the reason the general dévissage engine
`Stacks.HighTwistDevissage.exists_isZero_hgroup_twist_of_descending_devissage` cannot be used,
is **uniformity in the grading**. That engine runs on one sheaf at a time and produces one
twist bound per sheaf; what [Stacks, Tag 0884] needs out of [Stacks, Tag 0897] is a single `d₀`
serving every homogeneous degree `n` at once. So the induction has to be carried out on whole
`ℤ`-indexed families of modules, with `∀ n` inside the existential quantifier over the twist —
which is what `Stacks.Coherent.exists_isZero_Hgroup_of_descending_devissage` below does.

## Main results

* `Stacks.Coherent.isZero_Hgroup_X₃_of_shortExact` — the missing third member of the
  `Hgroup`-spelled long exact sequence trio: for a short exact sequence `0 → F₁ → F₂ → F₃ → 0`
  of `𝒪_X`-modules, `Hᵖ(X, F₂) = 0` and `Hᵖ⁺¹(X, F₁) = 0` force `Hᵖ(X, F₃) = 0`. The library
  carries the `X₂` form (`Stacks.SerreAffinenessCriterion.isZero_hgroup_of_shortExact`) but not
  this one.
* `Stacks.Coherent.isZero_Hgroup_tensorPowModule_X₃_of_shortExact` — the same after twisting by
  `L ^⊗ d`, which is exact because tensoring by an invertible module is an autoequivalence
  (`Stacks.AmpleCohomologicalCriterion.shortExact_map_tensorRight`).
* `Stacks.Coherent.exists_isZero_Hgroup_of_descending_devissage` — **the induction**. For a class
  of `ℤ`-indexed families of `𝒪_X`-modules which is acyclic above a fixed degree `e` and admits
  a dévissage step in every positive degree, there is one twist bound `d₀` beyond which *all*
  positive-degree cohomology of *all* twists of *all* members of the family vanishes.
* `Stacks.Coherent.devissageStep_of_shortExact` — the dévissage step in the shape it is actually
  produced in: a degreewise short exact sequence whose middle term is eventually acyclic in all
  positive degrees, uniformly in the degree.
* `Stacks.Coherent.exists_isZero_Hgroup_piece_tensorPowModule_of_devissage` — **part (2) of
  [Stacks, Tag 0897] for a sheaf of graded algebras with finite pieces, modulo the dévissage.**
  Everything cohomological is discharged; the single remaining hypothesis `hdev` asks for the
  short exact sequence of graded modules whose middle term has uniformly acyclic twists.
* `Stacks.Coherent.hasAssociatedGradedTwistVanishing_of_devissage` — the same read at the
  associated graded algebra of an ideal sheaf, where the finiteness of the pieces is
  `Stacks.Coherent.moduleFinite_algebraPiece`; that is the shape [Stacks, Tag 0884] consumes.

## What `hdev` still needs, and why it is not here

`hdev` is the construction the source performs by base change to `Spec_X 𝓑`. The route this
library is set up for instead presents a finite-type graded module over a graded algebra `𝓟`
with *free* homogeneous pieces, mapping onto `𝓑`; the module-level restriction along such a
surjection is
`SheafOfModules.GradedModule.restrictScalars`
(`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedModuleRestrictScalars.lean`) and the
transfer of finite type across it is
`Stacks.Coherent.isFiniteTypeOnAffine_restrictScalars`
(`StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionProjectiveEquivalenceAuxGraded.lean`).
That transfer is what makes the theorem above worth stating over an arbitrary `𝓟`: a graded
`𝓑`-module enters the induction as a graded `𝓟`-module with literally the same pieces, so the
conclusion needs no transport back. The two steps are taken in
`StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionProjectiveEquivalenceAuxPresentation.lean`.

## Implementation notes

**The bound.** The conclusion asks for one `d₀` valid in every positive cohomological degree.
Above `e` the vanishing is unconditional, so only the finitely many degrees `1, …, e` contribute
a bound, and their maximum is taken through `Int.toNat` over `Finset.range (e + 1)`:
`Int.self_le_toNat` makes each individual bound at most the maximum.

**The induction.** Descending induction on the cohomological degree is run as ordinary induction
on a slack variable `j` with the invariant `e + 1 ≤ p + j`; the base case is `e < p`, where the
hypothesis `hbound` applies, and the step turns the induction hypothesis at `p + 1` into the
statement at `p` through the dévissage. Since the kernel of the dévissage changes with each
step, the statement being inducted on is quantified over *all* members of the class, not just
the one at hand.

## References

* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 0884](https://stacks.math.columbia.edu/tag/0884)
* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
* [Stacks Project, Tag 010Q](https://stacks.math.columbia.edu/tag/010Q)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Ample Stacks.RelativeVeryAmple

universe u

namespace Stacks.Coherent

attribute [local instance] HasDerivedCategory.standard

/-! ### The third member of the long exact sequence -/

/-- **`Hᵖ(X, F₃)` vanishes when `Hᵖ(X, F₂)` and `Hᵖ⁺¹(X, F₁)` do.**

This is exactness of `Hᵖ(X, F₂) → Hᵖ(X, F₃) → Hᵖ⁺¹(X, F₁)`: the first map is zero because its
source is, so the connecting map is a monomorphism, and a monomorphism into a zero object has
zero source. The long exact sequence is the right derived δ-functor of `Γ(X, -)`, discharged by
`Stacks.CohomologyVanishing.isCohomologyDeltaFunctor_rightDerived`.

The degree is required positive because the δ-functor's degree-zero part is `Γ(X, -)` rather
than `H⁰(X, -)`; the two are compared by
`Stacks.HighTwistDevissage.isZero_hgroup_iff_isZero_functor_obj`, which carries that guard. -/
public theorem isZero_Hgroup_X₃_of_shortExact (X : Scheme.{u})
    {S : ShortComplex X.Modules} (hS : S.ShortExact) (p : ℕ) (hp : 0 < p)
    (h₂ : IsZero (Hgroup X.ringCatSheaf ⊤ p S.X₂))
    (h₁ : IsZero (Hgroup X.ringCatSheaf ⊤ (p + 1) S.X₁)) :
    IsZero (Hgroup X.ringCatSheaf ⊤ p S.X₃) := by
  have hD := Stacks.CohomologyVanishing.isCohomologyDeltaFunctor_rightDerived X.ringCatSheaf
    (⊤ : X.Opens)
  refine (Stacks.HighTwistDevissage.isZero_hgroup_iff_isZero_functor_obj
    X.ringCatSheaf hD hp _).1 ?_
  exact Stacks.AlgebraicGeometry.LerayAffineBase.isZero_obj_X₃ _ hS p
    ((Stacks.HighTwistDevissage.isZero_hgroup_iff_isZero_functor_obj
      X.ringCatSheaf hD hp _).2 h₂)
    ((Stacks.HighTwistDevissage.isZero_hgroup_iff_isZero_functor_obj
      X.ringCatSheaf hD (by omega) _).2 h₁)

/-- **`Stacks.Coherent.isZero_Hgroup_X₃_of_shortExact` after twisting by `L ^⊗ d`.**
Tensoring by an invertible module is an autoequivalence of `𝒪_X`-modules, so it carries the
short exact sequence to a short exact sequence. -/
public theorem isZero_Hgroup_tensorPowModule_X₃_of_shortExact (X : Scheme.{u}) (L : X.Modules)
    [IsInvertibleModule X L] (d : ℤ) (p : ℕ) (hp : 0 < p)
    {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (h₂ : IsZero (Hgroup X.ringCatSheaf ⊤ p (tensorModules X S.X₂ (tensorPowModule X L d))))
    (h₁ : IsZero (Hgroup X.ringCatSheaf ⊤ (p + 1)
      (tensorModules X S.X₁ (tensorPowModule X L d)))) :
    IsZero (Hgroup X.ringCatSheaf ⊤ p (tensorModules X S.X₃ (tensorPowModule X L d))) :=
  isZero_Hgroup_X₃_of_shortExact X (Stacks.AmpleCohomologicalCriterion.shortExact_map_tensorRight
    X (tensorPowModule X L d) hS) p hp h₂ h₁

/-! ### The descending induction, uniform in the grading -/

/-- **Descending dévissage with a bound uniform in the grading.**

Let `pieces M : ℤ → X.Modules` be the homogeneous pieces of a member `M` of a class `Good`, let
`L` be an invertible `𝒪_X`-module, and suppose

* `hbound`: `Hᵖ(X, (pieces M n) ⊗ L ^⊗ d) = 0` for every member `M`, every `p > e`, every degree
  `n` and every twist `d` — one `e` for all of them; and
* `step`: every member `M` admits, in every positive cohomological degree `p`, a member `R` and
  a twist bound `d₁` beyond which the vanishing of `Hᵖ⁺¹` on the pieces of `R` forces the
  vanishing of `Hᵖ` on the pieces of `M`, in every degree `n`.

Then every member `M` has a single twist bound `d₀` beyond which `Hᵖ(X, (pieces M n) ⊗ L ^⊗ d)`
vanishes for every positive `p` and every degree `n`.

`step` is the long exact sequence of a dévissage `0 → R → P → M → 0` with `P` acyclic; see
`Stacks.Coherent.devissageStep_of_shortExact`, which produces it from exactly that datum. -/
public theorem exists_isZero_Hgroup_of_descending_devissage {X : Scheme.{u}} (L : X.Modules)
    [IsInvertibleModule X L] {ι : Type*} (pieces : ι → ℤ → X.Modules) (Good : ι → Prop) (e : ℕ)
    (hbound : ∀ M : ι, Good M → ∀ p : ℕ, e < p → ∀ n d : ℤ,
      IsZero (Hgroup X.ringCatSheaf ⊤ p
        (tensorModules X (pieces M n) (tensorPowModule X L d))))
    (step : ∀ M : ι, Good M → ∀ p : ℕ, 0 < p → ∃ R : ι, Good R ∧ ∃ d₁ : ℤ,
      ∀ d : ℤ, d₁ ≤ d → ∀ n : ℤ,
        IsZero (Hgroup X.ringCatSheaf ⊤ (p + 1)
          (tensorModules X (pieces R n) (tensorPowModule X L d))) →
        IsZero (Hgroup X.ringCatSheaf ⊤ p
          (tensorModules X (pieces M n) (tensorPowModule X L d))))
    (M : ι) (hM : Good M) :
    ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d → ∀ p : ℕ, 0 < p → ∀ n : ℤ,
      IsZero (Hgroup X.ringCatSheaf ⊤ p
        (tensorModules X (pieces M n) (tensorPowModule X L d))) := by
  classical
  have key : ∀ j p : ℕ, 0 < p → e + 1 ≤ p + j → ∀ N : ι, Good N →
      ∃ c : ℤ, ∀ d : ℤ, c ≤ d → ∀ n : ℤ,
        IsZero (Hgroup X.ringCatSheaf ⊤ p
          (tensorModules X (pieces N n) (tensorPowModule X L d))) := by
    intro j
    induction j with
    | zero =>
        exact fun p _ hle N hN => ⟨0, fun d _ n => hbound N hN p (by omega) n d⟩
    | succ j ih =>
        intro p hp hle N hN
        rcases lt_or_ge e p with hep | hep
        · exact ⟨0, fun d _ n => hbound N hN p hep n d⟩
        · obtain ⟨R, hR, d₁, hd₁⟩ := step N hN p hp
          obtain ⟨d₂, hd₂⟩ := ih (p + 1) (by omega) (by omega) R hR
          exact ⟨max d₁ d₂, fun d hd n => hd₁ d (le_trans (le_max_left _ _) hd) n
            (hd₂ d (le_trans (le_max_right _ _) hd) n)⟩
  have main : ∀ q : ℕ, ∃ c : ℤ, ∀ d : ℤ, c ≤ d → ∀ n : ℤ,
      IsZero (Hgroup X.ringCatSheaf ⊤ (q + 1)
        (tensorModules X (pieces M n) (tensorPowModule X L d))) :=
    fun q => key (e + 1) (q + 1) (by omega) (by omega) M hM
  choose c hc using main
  refine ⟨(((Finset.range (e + 1)).sup fun q => (c q).toNat : ℕ) : ℤ), fun d hd p hp n => ?_⟩
  rcases lt_or_ge e p with hep | hep
  · exact hbound M hM p hep n d
  · obtain ⟨q, rfl⟩ : ∃ q : ℕ, p = q + 1 := ⟨p - 1, by omega⟩
    refine hc q d (le_trans ?_ hd) n
    refine le_trans (Int.self_le_toNat (c q)) ?_
    exact_mod_cast Finset.le_sup (f := fun r : ℕ => (c r).toNat)
      (Finset.mem_range.2 (by omega))

/-- **The dévissage step, in the shape it is produced in.** A degreewise short exact sequence
`0 → R n → (S n).X₂ → M n → 0` whose middle term is acyclic in all positive degrees for all
large twists, uniformly in `n`, supplies the `step` hypothesis of
`Stacks.Coherent.exists_isZero_Hgroup_of_descending_devissage`. -/
public theorem devissageStep_of_shortExact {X : Scheme.{u}} (L : X.Modules)
    [IsInvertibleModule X L] (Mp Rp : ℤ → X.Modules) (S : ℤ → ShortComplex X.Modules)
    (hSE : ∀ n : ℤ, (S n).ShortExact) (hX₁ : ∀ n : ℤ, (S n).X₁ = Rp n)
    (hX₃ : ∀ n : ℤ, (S n).X₃ = Mp n) (d₁ : ℤ)
    (hacyc : ∀ d : ℤ, d₁ ≤ d → ∀ m : ℕ, 0 < m → ∀ n : ℤ,
      IsZero (Hgroup X.ringCatSheaf ⊤ m
        (tensorModules X (S n).X₂ (tensorPowModule X L d))))
    (p : ℕ) (hp : 0 < p) (d : ℤ) (hd : d₁ ≤ d) (n : ℤ)
    (hR : IsZero (Hgroup X.ringCatSheaf ⊤ (p + 1)
      (tensorModules X (Rp n) (tensorPowModule X L d)))) :
    IsZero (Hgroup X.ringCatSheaf ⊤ p
      (tensorModules X (Mp n) (tensorPowModule X L d))) := by
  rw [← hX₃ n]
  refine isZero_Hgroup_tensorPowModule_X₃_of_shortExact X L d p hp (hSE n)
    (hacyc d hd p hp n) ?_
  rw [hX₁ n]
  exact hR

/-! ### Part (2) of [Stacks, Tag 0897] for a graded algebra sheaf, modulo the dévissage -/

/-- **Part (2) of [Stacks, Tag 0897] for a sheaf of graded algebras, with the dévissage as the
single hypothesis.**

Let `A` be Noetherian, `f : X ⟶ Spec A` proper, `L` an invertible `𝒪_X`-module, and let `𝓟` be a
sheaf of graded algebras on `X` whose homogeneous pieces have finite modules of sections over
affine opens (`hP`). Assume that every quasi-coherent graded `𝓟`-module `M` of finite type on
affine opens fits in a degreewise short exact sequence `0 → R → P → M → 0` with `R` again
quasi-coherent of finite type and with the twists of `P` acyclic in all positive degrees for all
large `d`, uniformly in the homogeneous degree. Then `M` itself has uniformly acyclic twists: one
`d₀` serves every positive cohomological degree and every homogeneous degree.

The cohomological degree bound `e` the induction descends from is [Stacks, Tag 01XJ] read on `X`
(`Stacks.AlgebraicGeometry.RelativeSerreVanishing.exists_isZero_hgroup_tensorPowTwist_of_lt`),
applicable because every homogeneous piece of such an `M` is coherent
(`Stacks.Coherent.isCoherent_piece`) — which is the only thing `hP` is spent on.

For the associated graded algebra of an ideal sheaf `hP` is
`Stacks.Coherent.moduleFinite_algebraPiece`; see
`Stacks.Coherent.hasAssociatedGradedTwistVanishing_of_devissage`. The dévissage itself is not
available at that algebra — its pieces are not free — so the hypothesis is discharged after
restricting scalars to an auxiliary graded algebra, in
`StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionProjectiveEquivalenceAuxPresentation.lean`.
-/
public theorem exists_isZero_Hgroup_piece_tensorPowModule_of_devissage
    (A : Type u) [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) [IsProper f] (L : X.Modules) [IsInvertibleModule X L]
    {P : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf}
    (hP : ∀ (U : X.affineOpens) (m : ℤ), Module.Finite Γ(X, U.1) Γ(algPiece P m, U.1))
    (hdev : ∀ M : SheafOfModules.GradedModule P,
      (∀ n : ℤ, (M.piece n).IsQuasicoherent) → IsFiniteTypeOnAffine M → ∀ p : ℕ, 0 < p →
      ∃ (R : SheafOfModules.GradedModule P) (S : ℤ → ShortComplex X.Modules),
        (∀ n : ℤ, (S n).ShortExact) ∧
        (∀ n : ℤ, (S n).X₁ = R.piece n) ∧ (∀ n : ℤ, (S n).X₃ = M.piece n) ∧
        (∀ n : ℤ, (R.piece n).IsQuasicoherent) ∧ IsFiniteTypeOnAffine R ∧
        ∃ d₁ : ℤ, ∀ d : ℤ, d₁ ≤ d → ∀ m : ℕ, 0 < m → ∀ n : ℤ,
          IsZero (Hgroup X.ringCatSheaf ⊤ m
            (tensorModules X (S n).X₂ (tensorPowModule X L d))))
    (M : SheafOfModules.GradedModule P)
    (hqc : ∀ n : ℤ, (M.piece n).IsQuasicoherent) (hft : IsFiniteTypeOnAffine M) :
    ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d → ∀ p : ℕ, 0 < p → ∀ n : ℤ,
      IsZero (Hgroup X.ringCatSheaf ⊤ p
        (tensorModules X (M.piece n) (tensorPowModule X L d))) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨e, he⟩ :=
    Stacks.AlgebraicGeometry.RelativeSerreVanishing.exists_isZero_hgroup_tensorPowTwist_of_lt f L
  refine exists_isZero_Hgroup_of_descending_devissage L
    (fun N : SheafOfModules.GradedModule P => N.piece)
    (fun N => (∀ n : ℤ, (N.piece n).IsQuasicoherent) ∧ IsFiniteTypeOnAffine N) e
    (fun N hN p hp n d => he p hp (N.piece n) (isCoherent_piece hP N hN.1 hN.2 n) d)
    (fun N hN p hp => ?_) M ⟨hqc, hft⟩
  obtain ⟨R, S, hSE, hX₁, hX₃, hRqc, hRft, d₁, hd₁⟩ := hdev N hN.1 hN.2 p hp
  exact ⟨R, ⟨hRqc, hRft⟩, d₁, fun d hd n hR =>
    devissageStep_of_shortExact L N.piece R.piece S hSE hX₁ hX₃ d₁ hd₁ p hp d hd n hR⟩

/-- **The hypothesis of [Stacks, Tag 0884] follows from the dévissage.**

`Stacks.Coherent.HasAssociatedGradedTwistVanishing` — part (2) of [Stacks, Tag 0897] for the
associated graded algebra of `I · 𝒪_X`, and the single hypothesis of
`Stacks.Coherent.exists_isZero_Hgroup_transitionKernel_tensorPowModule` — holds as soon as every
quasi-coherent finite-type graded module over such an algebra admits, in every positive
cohomological degree, a degreewise short exact sequence with quasi-coherent finite-type kernel
and uniformly acyclic middle term.

Ampleness of `L` is not used: the induction descends from [Stacks, Tag 01XJ], which needs only
properness. It is retained in the conclusion because the statement being produced carries it, and
because the construction of the dévissage is where ampleness is spent. -/
public theorem hasAssociatedGradedTwistVanishing_of_devissage
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f] (L : X.Modules)
    [IsInvertibleModule X L]
    (hdev : ∀ (D : AssociatedGradedAlgebraData
        (Stacks.Cohomology.FormalFunctions.baseIdealSheaf A I f))
      (M : SheafOfModules.GradedModule D.algebra),
      (∀ n : ℤ, (M.piece n).IsQuasicoherent) → IsFiniteTypeOnAffine M → ∀ p : ℕ, 0 < p →
      ∃ (R : SheafOfModules.GradedModule D.algebra) (S : ℤ → ShortComplex X.Modules),
        (∀ n : ℤ, (S n).ShortExact) ∧
        (∀ n : ℤ, (S n).X₁ = R.piece n) ∧ (∀ n : ℤ, (S n).X₃ = M.piece n) ∧
        (∀ n : ℤ, (R.piece n).IsQuasicoherent) ∧ IsFiniteTypeOnAffine R ∧
        ∃ d₁ : ℤ, ∀ d : ℤ, d₁ ≤ d → ∀ m : ℕ, 0 < m → ∀ n : ℤ,
          IsZero (Hgroup X.ringCatSheaf ⊤ m
            (tensorModules X (S n).X₂ (tensorPowModule X L d)))) :
    HasAssociatedGradedTwistVanishing A I f L := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  exact fun _ D M hqc hft =>
    exists_isZero_Hgroup_piece_tensorPowModule_of_devissage A f L
      (moduleFinite_algebraPiece D) (hdev D) M hqc hft

end Stacks.Coherent

end
