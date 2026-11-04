module

public import StacksFrontier.AlgebraicGeometry.HighTwistDevissage.Descending
public import StacksFrontier.AlgebraicGeometry.SectionsExact.Discharge

/-!
# Descending dévissage in the cohomology of `𝒪_X`-modules

`StacksFrontier/AlgebraicGeometry/HighTwistDevissage/Descending.lean` proves the descending
dévissage principle for an abstract cohomological δ-functor. This file instantiates it at
`Hⁿ(U, -)`, the `ℕ`-indexed right derived functors of `Γ(U, -)` on `Mod(𝒪_X)` of Tag 01E3
(`Hfunctor`), which is the form the cohomological arguments of Chapter 30
need:

> Let `P` be a class of `𝒪_X`-modules. If `Hᵖ(U, F) = 0` for every `F` in `P` and every `p > e`,
> and every `F` in `P` is the quotient term of a short exact sequence `0 → F' → G → F → 0` with
> `F'` again in `P` and `G` acyclic over `U` in positive degrees, then `Hᵖ(U, F) = 0` for every
> `F` in `P` and every `p > 0`.

The bound `e` is in practice read off a finite affine cover ([Stacks, Tag 01XI]); the short exact
sequence is produced by an ample twist ([Stacks, Tag 0EBD], [Stacks, Tag 01Q3]) or by a surjection
from a finite direct sum of twists ([Stacks, Tag 01YS] part (1), [Stacks, Tag 0B5Q] part (1)).

## Main results

* `Stacks.HighTwistDevissage.isZero_hgroup_iff_isZero_functor_obj`: in positive degrees, the
  positive-degree part of a cohomology δ-functor vanishes on a module exactly when the cohomology
  group does.
* `Stacks.HighTwistDevissage.isZero_hgroup_of_descending_devissage_of_deltaFunctor`: the
  principle above, from an arbitrary witness of
  `Stacks.CohomologyVanishing.IsCohomologyDeltaFunctor`.
* `Stacks.HighTwistDevissage.isZero_hgroup_of_descending_devissage`: the same with the δ-functor
  discharged by `Stacks.CohomologyVanishing.isCohomologyDeltaFunctor_rightDerived`, so that the
  long exact cohomology sequence is no longer a hypothesis. This is the usable form.
* `Stacks.HighTwistDevissage.exists_isZero_hgroup_twist_of_descending_devissage`: the twisted
  form, concluding vanishing on all sufficiently large twists. This is the shape of
  [Stacks, Tag 01YS] part (4) and [Stacks, Tag 0B5Q] part (3).

## Implementation notes

**Why the δ-functor is a parameter in the first version.** Discharging it costs the two
`HasDerivedCategory` instances that
`Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives` needs — the long exact
sequence for the `ℕ`-indexed `CategoryTheory.Functor.rightDerived` is built through `D⁺`. A
consumer that has a δ-functor from elsewhere, or that is working over a site where the derived
category has been constructed by hand, should use the parametrised version and pay nothing.

**The degree bookkeeping.** `Stacks.CohomologyVanishing.IsCohomologyDeltaFunctor` identifies
`D.functor (m + 1)` with `Hfunctor R U (m + 1)` and `D.functor 0` with `Γ(U, -)`, not with
`H⁰(U, -)`; the two differ by `CategoryTheory.Functor.rightDerivedZeroIsoSelf`. So every
translation below is guarded by `0 < p` and goes through `p = m + 1`. The vanishing bound needs
no guard of its own: `e < p` already forces `p ≥ 1`.

No tag attribute is attached: this is an engine for several tags of Chapter 30 and the statement
of none of them.

## References

* [Stacks Project, Tag 010Q](https://stacks.math.columbia.edu/tag/010Q)
* [Stacks Project, Tag 0EBD](https://stacks.math.columbia.edu/tag/0EBD)
* [Stacks Project, Tag 01YS](https://stacks.math.columbia.edu/tag/01YS)
* [Stacks Project, Tag 0B5Q](https://stacks.math.columbia.edu/tag/0B5Q)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u w

namespace Stacks.HighTwistDevissage

variable {X : Type u} [TopologicalSpace X]
  (R : Sheaf (Opens.grothendieckTopology X) RingCat)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{w}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [EnoughInjectives (SheafOfModules.{w} R)]

/-- In a positive degree, the degree-`p` part of a cohomology δ-functor over `U` vanishes on `F`
exactly when `Hᵖ(U, F)` does. -/
theorem isZero_hgroup_iff_isZero_functor_obj {U : Opens X}
    {D : DeltaFunctor (SheafOfModules.{w} R) AddCommGrpCat}
    (hD : Stacks.CohomologyVanishing.IsCohomologyDeltaFunctor R U D) {p : ℕ} (hp : 0 < p)
    (F : SheafOfModules.{w} R) : IsZero ((D.functor p).obj F) ↔ IsZero (Hgroup R U p F) := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, p = m + 1 := ⟨p - 1, by omega⟩
  exact ((hD.isoSucc m).app F).isZero_iff

/-- **Descending dévissage for the cohomology of `𝒪_X`-modules**, from a witness of the long
exact cohomology sequence over `U`.

If `Hᵖ(U, -)` vanishes on the class `P` above the degree `e`, and every member of `P` is the
quotient term of a short exact sequence whose middle term is acyclic over `U` in positive degrees
and whose first term is again in `P`, then `Hᵖ(U, -)` vanishes on `P` in every positive
degree. -/
theorem isZero_hgroup_of_descending_devissage_of_deltaFunctor {U : Opens X}
    {D : DeltaFunctor (SheafOfModules.{w} R) AddCommGrpCat}
    (hD : Stacks.CohomologyVanishing.IsCohomologyDeltaFunctor R U D)
    (P : SheafOfModules.{w} R → Prop) (e : ℕ)
    (hbound : ∀ p : ℕ, e < p → ∀ F : SheafOfModules.{w} R, P F → IsZero (Hgroup R U p F))
    (step : ∀ F : SheafOfModules.{w} R, P F →
      ∃ S : ShortComplex (SheafOfModules.{w} R), S.ShortExact ∧ S.X₃ = F ∧ P S.X₁ ∧
        ∀ m : ℕ, 0 < m → IsZero (Hgroup R U m S.X₂))
    (p : ℕ) (hp : 0 < p) (F : SheafOfModules.{w} R) (hF : P F) : IsZero (Hgroup R U p F) := by
  refine (isZero_hgroup_iff_isZero_functor_obj R hD hp F).1
    (isZero_obj_of_descending_devissage D P e ?_ ?_ p hp F hF)
  · intro q hq G hG
    exact (isZero_hgroup_iff_isZero_functor_obj R hD (by omega) G).2 (hbound q hq G hG)
  · intro G hG
    obtain ⟨S, hS, hX₃, hP₁, hacyc⟩ := step G hG
    refine ⟨S, hS, hX₃, hP₁, fun m hm ↦ ?_⟩
    exact (isZero_hgroup_iff_isZero_functor_obj R hD hm S.X₂).2 (hacyc m hm)

variable [HasDerivedCategory (SheafOfModules.{w} R)] [HasDerivedCategory AddCommGrpCat.{w}]

/-- **Descending dévissage for the cohomology of `𝒪_X`-modules**, with the long exact cohomology
sequence discharged by
`Stacks.CohomologyVanishing.isCohomologyDeltaFunctor_rightDerived`.

If `Hᵖ(U, F) = 0` for every `F` in `P` and every `p > e`, and every `F` in `P` is the quotient
term of a short exact sequence `0 → F' → G → F → 0` with `F'` again in `P` and `Hᵐ(U, G) = 0` for
all `m > 0`, then `Hᵖ(U, F) = 0` for every `F` in `P` and every `p > 0`. -/
theorem isZero_hgroup_of_descending_devissage (U : Opens X)
    (P : SheafOfModules.{w} R → Prop) (e : ℕ)
    (hbound : ∀ p : ℕ, e < p → ∀ F : SheafOfModules.{w} R, P F → IsZero (Hgroup R U p F))
    (step : ∀ F : SheafOfModules.{w} R, P F →
      ∃ S : ShortComplex (SheafOfModules.{w} R), S.ShortExact ∧ S.X₃ = F ∧ P S.X₁ ∧
        ∀ m : ℕ, 0 < m → IsZero (Hgroup R U m S.X₂))
    (p : ℕ) (hp : 0 < p) (F : SheafOfModules.{w} R) (hF : P F) : IsZero (Hgroup R U p F) :=
  isZero_hgroup_of_descending_devissage_of_deltaFunctor R
    (Stacks.CohomologyVanishing.isCohomologyDeltaFunctor_rightDerived R U) P e hbound step p hp
    F hF

/-- **Twisted descending dévissage for the cohomology of `𝒪_X`-modules.** The conclusion is
vanishing of `Hᵖ(U, T d F)` for all sufficiently large `d`, from a vanishing bound on all twists
and a dévissage sequence whose twists are all short exact and whose middle term is eventually
acyclic.

This is the form [Stacks, Tag 01YS] part (4) and [Stacks, Tag 0B5Q] part (3) are stated in: there
`T d` is the twist by the `d`-th power of the twisting sheaf on `Proj`, `P` is coherence, and the
dévissage sequence is the kernel sequence of a surjection from a finite direct sum of twists.
Instantiating it needs the twist to be available as a *functor* `T d : Mod(𝒪_X) ⥤ Mod(𝒪_X)`
preserving zero morphisms; at this pin the twist of a module sheaf on `Proj`
(`AlgebraicGeometry.ProjectiveSpectrum.Proj.twistSheafOfModules`) is a function of the module and
not a functor, so that functor is the missing input, not this lemma. -/
theorem exists_isZero_hgroup_twist_of_descending_devissage (U : Opens X)
    (T : ℤ → SheafOfModules.{w} R ⥤ SheafOfModules.{w} R)
    [∀ d : ℤ, (T d).PreservesZeroMorphisms] (P : SheafOfModules.{w} R → Prop) (e : ℕ)
    (hbound : ∀ p : ℕ, e < p → ∀ F : SheafOfModules.{w} R, P F → ∀ d : ℤ,
      IsZero (Hgroup R U p ((T d).obj F)))
    (step : ∀ F : SheafOfModules.{w} R, P F →
      ∃ S : ShortComplex (SheafOfModules.{w} R), S.X₃ = F ∧ P S.X₁ ∧
        (∀ d : ℤ, (S.map (T d)).ShortExact) ∧
        ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d → ∀ m : ℕ, 0 < m →
          IsZero (Hgroup R U m ((T d).obj S.X₂)))
    (p : ℕ) (hp : 0 < p) (F : SheafOfModules.{w} R) (hF : P F) :
    ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d → IsZero (Hgroup R U p ((T d).obj F)) := by
  have hD := Stacks.CohomologyVanishing.isCohomologyDeltaFunctor_rightDerived R U
  obtain ⟨d₀, hd₀⟩ := exists_isZero_obj_twist_of_descending_devissage
    (Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives (secF R U)) T P e
    (fun q hq G hG d =>
      (isZero_hgroup_iff_isZero_functor_obj R hD (by omega) _).2 (hbound q hq G hG d))
    (fun G hG => by
      obtain ⟨S, hX₃, hP₁, hSE, d₂, hd₂⟩ := step G hG
      exact ⟨S, hX₃, hP₁, hSE, d₂, fun d hd m hm =>
        (isZero_hgroup_iff_isZero_functor_obj R hD hm _).2 (hd₂ d hd m hm)⟩)
    p hp F hF
  exact ⟨d₀, fun d hd => (isZero_hgroup_iff_isZero_functor_obj R hD hp _).1 (hd₀ d hd)⟩

end Stacks.HighTwistDevissage

end
