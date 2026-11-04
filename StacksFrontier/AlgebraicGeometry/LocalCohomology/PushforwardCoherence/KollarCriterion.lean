module

public import StacksFrontier.AlgebraicGeometry.CoherentPushforwardCriteria.ClosedImmersionCoherence
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CoherentPushforwardCriterion
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CompletedLocalObstruction
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.PushforwardCoherence.ClosureSubscheme

/-!
# Kollár's coherence criterion for an open pushforward

Let `j : U ⟶ X` be an open immersion of locally Noetherian schemes and `F` a coherent
`𝒪_U`-module. [Stacks, Tag 0BK3] (Kollár's criterion) says that `j_*F` is coherent if and only if
for every associated point `x` of `F`, every point `w` of the reduced closure `Z_x` of `{j x}` in
`X` lying outside the image of `j`, and every associated prime `𝔭` of the completed local ring
`𝒪^∧_{Z_x, w}`, one has `2 ≤ dim(𝒪^∧_{Z_x, w} ⧸ 𝔭)`.

This file proves the two reductions by which that equivalence follows from [Stacks, Tag 0BJZ] and
[Stacks, Tag 0BK1], and assembles the criterion from them. Both reductions are unconditional; the
assembled criterion carries those two tags as explicit hypotheses. [Stacks, Tag 0BJZ] is in the
library, and
`StacksFrontier.AlgebraicGeometry.LocalCohomology.PushforwardCoherence.KollarCriterionAssembled`
discharges that hypothesis, leaving [Stacks, Tag 0BK1] the only one.

## Main results

* `Stacks.LocalCohomology.notMem_range_pointClosure_iff`: the hinge both directions turn on — a
  point of the reduced closure of `{j x}` lies outside the image of the open immersion `j'` of
  point closures exactly when its image in `X` lies outside the image of `j`.
* `Stacks.LocalCohomology.two_le_ringKrullDim_quotient_adicCompletion_stalk_pointClosure`: **the
  forward reduction.** Coherence of the direct image to `X` of the structure sheaf of the reduced
  closure of a point `x` of `U` forces the dimension bound of [Stacks, Tag 0BK3] at every point of
  the reduced closure of `{j x}` outside the image of `j`. This is the whole content of the
  forward implication of that tag at a single associated point; the only further input the tag
  needs is the forward implication of [Stacks, Tag 0BJZ], which collects the associated points.
* `Stacks.LocalCohomology.isCoherent_pushforward_pointClosure_of_isCoherent_pushforward_closure`:
  **the backward reduction.** Coherence of the direct image of the structure sheaf of the reduced
  closure of `x` along the open immersion `j'` of point closures — which is what
  [Stacks, Tag 0BK1] produces out of the dimension bound — gives coherence of its direct image to
  `X`, which is what [Stacks, Tag 0BJZ] consumes.
* `Stacks.LocalCohomology.isCoherent_pushforward_iff_forall_two_le_ringKrullDim_of_pointClosure`:
  **[Stacks, Tag 0BK3] granted [Stacks, Tag 0BJZ] and [Stacks, Tag 0BK1]**, both as explicit
  hypotheses. Nothing else is assumed. The first is discharged in
  `StacksFrontier.AlgebraicGeometry.LocalCohomology.PushforwardCoherence.KollarCriterionAssembled`.

## Implementation notes

No `@[stacks 0BK3]` attribute is attached to anything here, and none may be: the criterion is not
proved. Its two inputs are the two hypotheses of
`isCoherent_pushforward_iff_forall_two_le_ringKrullDim_of_pointClosure`; the first is in the
library, the second is not.

* [Stacks, Tag 0BJZ] (Lemma 51.8.1) reduces coherence of `j_*F` to coherence of the direct images
  of the structure sheaves of the reduced closures of the associated points of `F`. It is proved by
  `isCoherent_pushforward_iff_forall_isAssociatedPoint` in the namespace
  `Stacks.AlgebraicGeometry.CoherenceFromPointClosures`, which constructs the comparison morphism
  `i_{x,*} 𝒪_{W_x} ⟶ F` out of `x ∈ Ass(F)` rather than assuming it. All of its inputs are present,
  among them the extension of a map of coherent modules across an open after multiplication by a
  power of a function, [Stacks, Tag 01YB]
  (`StacksFrontier.AlgebraicGeometry.Coherent.HomColimit.GlobalSections`), and [Stacks, Tag 01Y4]
  (`StacksDraft.AlgebraicGeometry.Cohomology.Coherent`), [Stacks, Tag 0AVL]
  (`StacksDraft.AlgebraicGeometry.AssociatedPointsMono`), [Stacks, Tag 05AE], [Stacks, Tag 05AF],
  [Stacks, Tag 01Y1] and [Stacks, Tag 01LC].
* [Stacks, Tag 0BK1] (Lemma 51.8.4) is the hard half. Three of its four steps are in
  `StacksFrontier.AlgebraicGeometry.LocalCohomology.CoherentPushforwardCriterionMain`; what is
  missing is the body of its induction, namely [Stacks, Tag 0AW9], [Stacks, Tag 0BK0],
  [Stacks, Tag 01YB] and [Stacks, Tag 0AWA]. [Stacks, Tag 0AW9] cannot even be stated here, since
  the library has no local cohomology *module* — see the module docstring of
  `StacksFrontier.AlgebraicGeometry.LocalCohomology.LocalFinitenessDescent`.

The reductions themselves use nothing beyond what is already in the library. The forward one is the
contrapositive of the obstruction of [Stacks, Tag 0AWC]
(`Stacks.LocalCohomology.not_isCoherent_pushforward_structureSheaf`) applied on the reduced
closure of `{j x}` rather than on `X`, together with the coherence equivalence of
[Stacks, Tag 0BK2]
(`Stacks.AlgebraicGeometry.ClosedImmersionCoherence.isCoherent_pushforward_pointClosure_iff`) and
the conversion of the failure of `2 ≤ dim` into the hypothesis `dim = 1` of that obstruction
(`Stacks.LocalCohomology.ringKrullDim_quotient_adicCompletion_stalk_eq_one_of_notMem_range`).
Because that form of [Stacks, Tag 0AWC] asks only for a *locally* Noetherian target, no
restriction to an affine open of the closure is needed, and with it no comparison of a direct
image with its restriction and no transport of associated primes along a stalk isomorphism.

The two shapes of the iterated direct image — `j_* i_{W,*} 𝒪_W` and `(i_W ≫ j)_* 𝒪_W` — are
interchanged by `AlgebraicGeometry.Scheme.Modules.pushforwardComp`; [Stacks, Tag 0BJZ] is stated
in the second and [Stacks, Tag 0BK2] in the first, so each reduction crosses that isomorphism
once.

## References

* [Stacks Project, Tag 0BK3](https://stacks.math.columbia.edu/tag/0BK3)
* [Stacks Project, Tag 0BJZ](https://stacks.math.columbia.edu/tag/0BJZ)
* [Stacks Project, Tag 0BK1](https://stacks.math.columbia.edu/tag/0BK1)
* [Stacks Project, Tag 0BK2](https://stacks.math.columbia.edu/tag/0BK2)
* [Stacks Project, Tag 0AWC](https://stacks.math.columbia.edu/tag/0AWC)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing
open Stacks.AlgebraicGeometry.ClosedImmersionCoherence
open Stacks.AlgebraicGeometry.CoherentDevissage (isCoherent_of_iso)

universe u

namespace Stacks.LocalCohomology

/-! ### The hinge: the two descriptions of the complement -/

/-- For an open immersion `j : U ⟶ X` and a point `x` of `U`, a point `w` of the reduced closure
of `{j x}` in `X` lies outside the image of the induced open immersion `j'` of point closures
exactly when its image in `X` lies outside the image of `j`.

This is `Stacks.LocalCohomology.range_closure_open_square` read as a membership criterion; it is
what lets the complement of `U` in `X` and the complement of the smaller point closure in the
larger be used interchangeably in [Stacks, Tag 0BK3]. -/
theorem notMem_range_pointClosure_iff {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    [IsLocallyNoetherian U] [IsLocallyNoetherian X] (x : U)
    (j' : (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({x} : Set U))).subscheme ⟶
      (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({j x} : Set X))).subscheme)
    (comm : j' ≫ (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({j x} : Set X))).subschemeι =
      (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({x} : Set U))).subschemeι ≫ j)
    (w : (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({j x} : Set X))).subscheme) :
    w ∉ Set.range j'.base ↔
      (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({j x} : Set X))).subschemeι.base w ∉ Set.range j.base := by
  rw [range_closure_open_square j x j' comm]
  exact Iff.rfl

/-! ### The forward reduction -/

/-- **The forward reduction of [Stacks, Tag 0BK3].** Let `j : U ⟶ X` be an open immersion of
locally Noetherian schemes and `x` a point of `U`. If the direct image to `X` of the structure
sheaf of the reduced closure `W` of `{x}` in `U` is coherent, then at every point `w` of the
reduced closure `Z` of `{j x}` in `X` whose image in `X` lies outside the image of `j`, every
associated prime `𝔭` of the completed local ring `𝒪^∧_{Z, w}` satisfies `2 ≤ dim(𝒪^∧_{Z, w} ⧸ 𝔭)`.

Together with the forward implication of [Stacks, Tag 0BJZ], which produces the hypothesis at
every associated point of a coherent module whose direct image is coherent, this is the forward
implication of [Stacks, Tag 0BK3].

The proof is the source's. The square of point closures of [Stacks, Tag 0BK2] provides an open
immersion `j' : W ⟶ Z`, and across its closed immersion `Z ⟶ X` coherence of `j_* i_{W,*} 𝒪_W` is
equivalent to coherence of `j'_* 𝒪_W`. Were some associated component of `𝒪^∧_{Z, w}` to have
dimension less than two it would have dimension exactly one, `Z` being integral and `w` not its
generic point, and then the obstruction of [Stacks, Tag 0AWC] at the open immersion `j'` of
integral locally Noetherian schemes would contradict that coherence. -/
theorem two_le_ringKrullDim_quotient_adicCompletion_stalk_pointClosure {U X : Scheme.{u}}
    [IsLocallyNoetherian U] [IsLocallyNoetherian X] (j : U ⟶ X) [IsOpenImmersion j] (x : U)
    (h : ((Scheme.Modules.pushforward ((Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure ({x} : Set U))).subschemeι ≫ j)).obj
        (SheafOfModules.unit.{u} (Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure ({x} : Set U))).subscheme.ringCatSheaf)).IsCoherent)
    {w : (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({j x} : Set X))).subscheme}
    (hw : (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({j x} : Set X))).subschemeι.base w ∉ Set.range j.base)
    {p : Ideal (AdicCompletion (maximalIdeal ((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({j x} : Set X))).subscheme.presheaf.stalk w))
      ((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({j x} : Set X))).subscheme.presheaf.stalk w))}
    (hp : IsAssociatedPrimeStacks
      (AdicCompletion (maximalIdeal ((Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure ({j x} : Set X))).subscheme.presheaf.stalk w))
        ((Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure ({j x} : Set X))).subscheme.presheaf.stalk w))
      (AdicCompletion (maximalIdeal ((Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure ({j x} : Set X))).subscheme.presheaf.stalk w))
        ((Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure ({j x} : Set X))).subscheme.presheaf.stalk w)) p) :
    (2 : WithBot ℕ∞) ≤ ringKrullDim (AdicCompletion
      (maximalIdeal ((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({j x} : Set X))).subscheme.presheaf.stalk w))
      ((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({j x} : Set X))).subscheme.presheaf.stalk w) ⧸ p) := by
  obtain ⟨j', hj', hcomm⟩ := Scheme.IdealSheafData.exists_isOpenImmersion_pointClosure j x
  have : IsIntegral (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({x} : Set U))).subscheme :=
    Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure x
  have : IsIntegral (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({j x} : Set X))).subscheme :=
    Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure (j x)
  have : IsLocallyNoetherian (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({j x} : Set X))).subscheme :=
    Scheme.IdealSheafData.isLocallyNoetherian_subscheme _
  have := h
  -- `j_* i_{W,*} 𝒪_W` is coherent, hence so is `j'_* 𝒪_W`.
  have hiter : ((Scheme.Modules.pushforward j).obj
      ((Scheme.Modules.pushforward (Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure ({x} : Set U))).subschemeι).obj
        (SheafOfModules.unit.{u} (Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure ({x} : Set U))).subscheme.ringCatSheaf))).IsCoherent :=
    isCoherent_of_iso
      ((Scheme.Modules.pushforwardComp (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({x} : Set U))).subschemeι j).app _)
  have hZ := (isCoherent_pushforward_pointClosure_iff j x j' hcomm).mp hiter
  -- The dimension bound at `w` is forced by the obstruction of [Stacks, Tag 0AWC] at `j'`.
  have hw' : w ∉ Set.range j'.base :=
    (notMem_range_pointClosure_iff j x j' hcomm w).mpr hw
  by_contra hdim
  exact not_isCoherent_pushforward_structureSheaf j'
    ⟨w, p, hw', hp,
      ringKrullDim_quotient_adicCompletion_stalk_eq_one_of_notMem_range j' hw' hp hdim⟩ hZ

/-! ### The backward reduction -/

/-- **The backward reduction of [Stacks, Tag 0BK3].** Let `j : U ⟶ X` be an open immersion of
locally Noetherian schemes, `x` a point of `U`, and `j'` the induced morphism from the reduced
closure `W` of `{x}` in `U` to the reduced closure `Z` of `{j x}` in `X`. Coherence of `j'_* 𝒪_W`
gives coherence of `(i_W ≫ j)_* 𝒪_W`.

The hypothesis is what [Stacks, Tag 0BK1] produces out of the dimension bound of
[Stacks, Tag 0BK3], and the conclusion is what the backward implication of [Stacks, Tag 0BJZ]
consumes, so this is the whole of the backward implication of [Stacks, Tag 0BK3] at a single
associated point.

It is the coherence equivalence of [Stacks, Tag 0BK2] followed by
`AlgebraicGeometry.Scheme.Modules.pushforwardComp`. -/
theorem isCoherent_pushforward_pointClosure_of_isCoherent_pushforward_closure {U X : Scheme.{u}}
    [IsLocallyNoetherian U] [IsLocallyNoetherian X] (j : U ⟶ X) [IsOpenImmersion j] (x : U)
    (j' : (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({x} : Set U))).subscheme ⟶
      (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({j x} : Set X))).subscheme)
    (comm : j' ≫ (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({j x} : Set X))).subschemeι =
      (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({x} : Set U))).subschemeι ≫ j)
    (h : ((Scheme.Modules.pushforward j').obj
      (SheafOfModules.unit.{u} (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({x} : Set U))).subscheme.ringCatSheaf)).IsCoherent) :
    ((Scheme.Modules.pushforward ((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({x} : Set U))).subschemeι ≫ j)).obj
      (SheafOfModules.unit.{u} (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({x} : Set U))).subscheme.ringCatSheaf)).IsCoherent := by
  -- Stated at the composite functor, which is where the isomorphism below asks for it.
  have : ((Scheme.Modules.pushforward (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({x} : Set U))).subschemeι ⋙ Scheme.Modules.pushforward j).obj
      (SheafOfModules.unit.{u} (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({x} : Set U))).subscheme.ringCatSheaf)).IsCoherent :=
    (isCoherent_pushforward_pointClosure_iff j x j' comm).mpr h
  exact isCoherent_of_iso
    ((Scheme.Modules.pushforwardComp (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({x} : Set U))).subschemeι j).app _).symm

/-! ### Kollár's criterion, granted its two missing inputs -/

/-- **Kollár's criterion, [Stacks, Tag 0BK3], granted [Stacks, Tag 0BJZ] and
[Stacks, Tag 0BK1].** Let `j : U ⟶ X` be an open immersion of locally Noetherian schemes and `F` a
coherent `𝒪_U`-module. Then `j_*F` is coherent if and only if for every associated point `x` of
`F`, every point `w` of the reduced closure of `{j x}` in `X` whose image lies outside the image
of `j`, and every associated prime `𝔭` of the completed local ring of that closure at `w`, one has
`2 ≤ dim` of the corresponding quotient.

The two hypotheses are [Stacks, Tag 0BJZ] at `j` and `F`, and [Stacks, Tag 0BK1] in full
generality. The first is proved and is discharged in
`StacksFrontier.AlgebraicGeometry.LocalCohomology.PushforwardCoherence.KollarCriterionAssembled`;
the second is not, which is why no `@[stacks 0BK3]` attribute is
attached. Everything else the criterion needs is proved: the forward implication is
`two_le_ringKrullDim_quotient_adicCompletion_stalk_pointClosure` and the backward one is
`isCoherent_pushforward_pointClosure_of_isCoherent_pushforward_closure`, with
`notMem_range_pointClosure_iff` translating the complement of `U` into the complement that
[Stacks, Tag 0BK1] is stated at. -/
theorem isCoherent_pushforward_iff_forall_two_le_ringKrullDim_of_pointClosure {U X : Scheme.{u}}
    [IsLocallyNoetherian U] [IsLocallyNoetherian X] (j : U ⟶ X) [IsOpenImmersion j]
    (F : U.Modules) [F.IsCoherent]
    (hBJZ : ((Scheme.Modules.pushforward j).obj F).IsCoherent ↔
      ∀ x : U, x ∈ Stacks.Divisors.associatedPoints F →
        ((Scheme.Modules.pushforward ((Scheme.IdealSheafData.vanishingIdeal
            (Closeds.closure ({x} : Set U))).subschemeι ≫ j)).obj
          (SheafOfModules.unit.{u} (Scheme.IdealSheafData.vanishingIdeal
            (Closeds.closure ({x} : Set U))).subscheme.ringCatSheaf)).IsCoherent)
    (hBK1 : ∀ (W Z : Scheme.{u}) (j' : W ⟶ Z), IsOpenImmersion j' → IsIntegral Z →
      IsLocallyNoetherian Z → Nonempty W →
      (∀ z : Z, z ∉ Set.range j'.base →
        ∀ q : Ideal (AdicCompletion (maximalIdeal (Z.presheaf.stalk z)) (Z.presheaf.stalk z)),
          IsAssociatedPrimeStacks
            (AdicCompletion (maximalIdeal (Z.presheaf.stalk z)) (Z.presheaf.stalk z))
            (AdicCompletion (maximalIdeal (Z.presheaf.stalk z)) (Z.presheaf.stalk z)) q →
          (2 : WithBot ℕ∞) ≤ ringKrullDim
            (AdicCompletion (maximalIdeal (Z.presheaf.stalk z)) (Z.presheaf.stalk z) ⧸ q)) →
      ((Scheme.Modules.pushforward j').obj
        (SheafOfModules.unit.{u} W.ringCatSheaf)).IsCoherent) :
    ((Scheme.Modules.pushforward j).obj F).IsCoherent ↔
      ∀ x : U, x ∈ Stacks.Divisors.associatedPoints F →
        ∀ w : (Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure ({j x} : Set X))).subscheme,
          (Scheme.IdealSheafData.vanishingIdeal
            (Closeds.closure ({j x} : Set X))).subschemeι.base w ∉ Set.range j.base →
          ∀ p : Ideal (AdicCompletion (maximalIdeal ((Scheme.IdealSheafData.vanishingIdeal
              (Closeds.closure ({j x} : Set X))).subscheme.presheaf.stalk w))
            ((Scheme.IdealSheafData.vanishingIdeal
              (Closeds.closure ({j x} : Set X))).subscheme.presheaf.stalk w)),
            IsAssociatedPrimeStacks
              (AdicCompletion (maximalIdeal ((Scheme.IdealSheafData.vanishingIdeal
                  (Closeds.closure ({j x} : Set X))).subscheme.presheaf.stalk w))
                ((Scheme.IdealSheafData.vanishingIdeal
                  (Closeds.closure ({j x} : Set X))).subscheme.presheaf.stalk w))
              (AdicCompletion (maximalIdeal ((Scheme.IdealSheafData.vanishingIdeal
                  (Closeds.closure ({j x} : Set X))).subscheme.presheaf.stalk w))
                ((Scheme.IdealSheafData.vanishingIdeal
                  (Closeds.closure ({j x} : Set X))).subscheme.presheaf.stalk w)) p →
            (2 : WithBot ℕ∞) ≤ ringKrullDim (AdicCompletion
              (maximalIdeal ((Scheme.IdealSheafData.vanishingIdeal
                (Closeds.closure ({j x} : Set X))).subscheme.presheaf.stalk w))
              ((Scheme.IdealSheafData.vanishingIdeal
                (Closeds.closure ({j x} : Set X))).subscheme.presheaf.stalk w) ⧸ p) := by
  refine ⟨fun hF x hx w hw p hp =>
      two_le_ringKrullDim_quotient_adicCompletion_stalk_pointClosure j x (hBJZ.mp hF x hx) hw hp,
    fun hdim => hBJZ.mpr fun x hx => ?_⟩
  obtain ⟨j', hj', hcomm⟩ := Scheme.IdealSheafData.exists_isOpenImmersion_pointClosure j x
  have : IsIntegral (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({x} : Set U))).subscheme :=
    Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure x
  have : IsIntegral (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({j x} : Set X))).subscheme :=
    Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure (j x)
  have : IsLocallyNoetherian (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({j x} : Set X))).subscheme :=
    Scheme.IdealSheafData.isLocallyNoetherian_subscheme _
  exact isCoherent_pushforward_pointClosure_of_isCoherent_pushforward_closure j x j' hcomm
    (hBK1 _ _ j' hj' inferInstance inferInstance inferInstance fun w hw p hp =>
      hdim x hx w ((notMem_range_pointClosure_iff j x j' hcomm w).mp hw) p hp)

end Stacks.LocalCohomology

end
