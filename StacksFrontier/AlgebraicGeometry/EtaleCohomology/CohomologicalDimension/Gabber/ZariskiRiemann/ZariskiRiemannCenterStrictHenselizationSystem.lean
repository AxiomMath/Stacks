module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.ZariskiRiemann.ZariskiRiemannCenterStrictHenselization
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.CompatibleSystem

/-!
# The canonical system of strict henselizations at the centers

Let `B` be a domain with fraction field `K`, `V ⊆ K` a valuation ring containing `B`, and fix a
separable algebraic closure `κ(V) ⊆ Ω` of the residue field of `V`. For each proper model `Y` of
`Spec K` over `Spec B` let `A_Y ⊆ V` be the image of the local ring at the center
(`AlgebraicGeometry.Scheme.ZariskiRiemann.centerRanges`), and `κ_Y^{sep}` the separable closure
of `κ(A_Y)` inside `Ω`. The strict henselizations `A_Y → A_Y^{sh}` with respect to `κ_Y^{sep}`
(Stacks 04GP), with the maps `A_Y^{sh} → A_{Y'}^{sh}` of Stacks 04GU inducing the inclusions
`κ_Y^{sep} ⊆ κ_{Y'}^{sep}`, form a directed system
(`Stacks.StrictHenselization.CompatibleSystem.exists_directedSystem_isStrictHenselization`).
Its colimit is a strict henselization of `V`
(`AlgebraicGeometry.Scheme.ZariskiRiemann.exists_isStrictHenselization_colimit_centerRanges`).
So `V^{sh} = colim_Y A_Y^{sh}` holds outright, with no system of strict henselizations assumed:
this is the identification of the stalk at a point of the Zariski–Riemann space in Gabber's
argument for Travaux de Gabber, Exposé XVIII-A, Corollary 1.2 (last remark of §2).

## Main results

In the namespace `AlgebraicGeometry.Scheme.ZariskiRiemann`:

* `exists_directedSystem_isStrictHenselization_centerRanges`: the `A_Y` have a directed system
  of strict henselizations over the inclusions `A_Y ⊆ A_{Y'}`.
* `exists_isStrictHenselization_directLimit_centerRanges`: **`V^{sh}` is the colimit of the
  `A_Y^{sh}`.**

## References

* [StacksProject 04GP](https://stacks.math.columbia.edu/tag/04GP)
* [StacksProject 04GU](https://stacks.math.columbia.edu/tag/04GU)
* [StacksProject 04GI](https://stacks.math.columbia.edu/tag/04GI)
* Travaux de Gabber sur l'uniformisation locale et la cohomologie étale des schémas
  quasi-excellents, Exposé XVIII-A (L. Illusie), last remark of §2, Astérisque 363–364 (2014)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing Stacks.StrictHenselization Stacks.StrictHenselization.DirectLimit

universe u v

namespace AlgebraicGeometry.Scheme.ZariskiRiemann

variable {B : Type u} [CommRing B] [IsDomain B] (V : ValuationSubring (FractionRing B))
  (hV : ∀ b : B, algebraMap B (FractionRing B) b ∈ V)

/-- The residue field map `κ(A_Y) → κ(V)` of the local inclusion `A_Y ⊆ V`. -/
def centerRangesResidueMap (a : centerRanges V hV) :
    (maximalIdeal a.1).ResidueField →+* (maximalIdeal V).ResidueField :=
  have := isLocalHom_centerRanges_subtype V hV a
  Ideal.ResidueField.map (maximalIdeal a.1) (maximalIdeal V) a.1.subtype
    (maximalIdeal_comap a.1.subtype).symm

/-- `centerRangesResidueMap` on a residue class. -/
theorem centerRangesResidueMap_algebraMap (a : centerRanges V hV) (x : a.1) :
    centerRangesResidueMap V hV a (algebraMap a.1 (maximalIdeal a.1).ResidueField x) =
      algebraMap V (maximalIdeal V).ResidueField x :=
  Ideal.ResidueField.map_algebraMap _ _ _ _ x

/-- **The `A_Y` have a directed system of strict henselizations.** Fix a separable algebraic
closure `κ` of the residue field of `V`. The strict henselizations `A_Y → A_Y^{sh}` with respect
to the separable closures `κ_Y^{sep}` of `κ(A_Y)` inside `κ`, and the maps of Stacks 04GU over the
inclusions `A_Y ⊆ A_{Y'}` inducing `κ_Y^{sep} ⊆ κ_{Y'}^{sep}`, form a directed system. -/
theorem exists_directedSystem_isStrictHenselization_centerRanges (κ : Type v) [Field κ]
    [Algebra (maximalIdeal V).ResidueField κ] [IsSepClosure (maximalIdeal V).ResidueField κ] :
    ∃ (Rsh : centerRanges V hV → Type u) (_ : ∀ a, CommRing (Rsh a))
      (_ : ∀ a, IsLocalRing (Rsh a)) (_ : ∀ a, Algebra a.1 (Rsh a))
      (κsep : centerRanges V hV → Type v) (_ : ∀ a, Field (κsep a))
      (_ : ∀ a, Algebra (maximalIdeal a.1).ResidueField (κsep a))
      (_ : ∀ a, IsSepClosure (maximalIdeal a.1).ResidueField (κsep a))
      (fsh : ∀ a b, a ≤ b → Rsh a →+* Rsh b),
      DirectedSystem Rsh (fun a b h => fsh a b h) ∧
        (∀ a, Nonempty (IsStrictHenselization a.1 (κsep a) (Rsh a))) ∧
        ∀ a b (hab : a ≤ b) x, fsh a b hab (algebraMap a.1 (Rsh a) x) =
          algebraMap b.1 (Rsh b)
            (subringInclusion (fun a : centerRanges V hV => a.1) (fun _ _ h => h) a b hab x) := by
  have : IsSepClosed κ := (isSepClosure_iff.mp ‹_›).1
  let A : centerRanges V hV → Subring V := fun a => a.1
  have hA : Monotone A := fun _ _ h => h
  have := directedSystem_subringInclusion A hA
  let : ∀ a : centerRanges V hV, Algebra (maximalIdeal a.1).ResidueField κ := fun a =>
    ((algebraMap (maximalIdeal V).ResidueField κ).comp (centerRangesResidueMap V hV a)).toAlgebra
  refine CompatibleSystem.exists_directedSystem_isStrictHenselization (subringInclusion A hA)
    (isLocalHom_subringInclusion_centerRanges V hV) κ fun a b hab r => ?_
  change algebraMap (maximalIdeal V).ResidueField κ (centerRangesResidueMap V hV b _) =
    algebraMap (maximalIdeal V).ResidueField κ (centerRangesResidueMap V hV a _)
  rw [centerRangesResidueMap_algebraMap, centerRangesResidueMap_algebraMap]
  rfl

/-- **The strict henselization of `V` is the colimit of the strict henselizations of the `A_Y`**
(unconditional form of
`AlgebraicGeometry.Scheme.ZariskiRiemann.exists_isStrictHenselization_colimit_centerRanges`).
For a separable algebraic closure `κ` of the residue field of `V` there are strict
henselizations `A_Y → A_Y^{sh}` and maps `A_Y^{sh} → A_{Y'}^{sh}` over the inclusions forming a
directed system, whose colimit is a local ring with a `V`-algebra structure, compatible with the
maps `A_Y → A_Y^{sh}`, for which it is a strict henselization of `V` with respect to `κ`. -/
theorem exists_isStrictHenselization_directLimit_centerRanges (κ : Type v) [Field κ]
    [Algebra (maximalIdeal V).ResidueField κ] [IsSepClosure (maximalIdeal V).ResidueField κ] :
    ∃ (Rsh : centerRanges V hV → Type u) (_ : ∀ a, CommRing (Rsh a))
      (_ : ∀ a, IsLocalRing (Rsh a)) (_ : ∀ a, Algebra a.1 (Rsh a))
      (κsep : centerRanges V hV → Type v) (_ : ∀ a, Field (κsep a))
      (_ : ∀ a, Algebra (maximalIdeal a.1).ResidueField (κsep a))
      (_ : ∀ a, IsSepClosure (maximalIdeal a.1).ResidueField (κsep a))
      (fsh : ∀ a b, a ≤ b → Rsh a →+* Rsh b) (_ : DirectedSystem Rsh fun a b h => fsh a b h)
      (_ : IsLocalRing (colimitRing Rsh fsh)) (_ : Algebra V (colimitRing Rsh fsh)),
      (∀ a, Nonempty (IsStrictHenselization a.1 (κsep a) (Rsh a))) ∧
        (∀ a b (hab : a ≤ b) x, fsh a b hab (algebraMap a.1 (Rsh a) x) =
          algebraMap b.1 (Rsh b)
            (subringInclusion (fun a : centerRanges V hV => a.1) (fun _ _ h => h) a b hab x)) ∧
        (∀ a (x : a.1), algebraMap V (colimitRing Rsh fsh) x =
          colimitOf Rsh fsh a (algebraMap a.1 (Rsh a) x)) ∧
        Nonempty (IsStrictHenselization V κ (colimitRing Rsh fsh)) := by
  obtain ⟨Rsh, ring, loc, alg, κsep, fld, algκ, sepκ, fsh, hds, hsh, hcomm⟩ :=
    exists_directedSystem_isStrictHenselization_centerRanges V hV κ
  obtain ⟨hloc, algV, hpin, hVsh⟩ :=
    exists_isStrictHenselization_colimit_centerRanges V hV fsh (fun a => (hsh a).some) hcomm κ
  exact ⟨Rsh, ring, loc, alg, κsep, fld, algκ, sepκ, fsh, hds, hloc, algV, hsh, hcomm, hpin,
    hVsh⟩

end AlgebraicGeometry.Scheme.ZariskiRiemann

end
