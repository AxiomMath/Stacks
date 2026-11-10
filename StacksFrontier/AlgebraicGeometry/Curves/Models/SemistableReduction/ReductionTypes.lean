module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.SemistableReduction.GoodReduction
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SemistableReduction.NodalMinimalModel
public import StacksFrontier.AlgebraicGeometry.Curves.Models.MinimalModelGenusZero
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.SmoothOfRelativeDimension

/-!
# Semistable and good reduction, read on minimal models

Let `R` be a discrete valuation ring with fraction field `K` and let `C` be a smooth projective
curve over `K` with `H⁰(C, 𝒪_C) = K`. This file proves [Stacks, Tag 0CDG] and
[Stacks, Tag 0CDI]: `C` has a proper model which is at-worst-nodal of relative dimension one
(resp. smooth) if and only if some minimal model is, if and only if every minimal model is.

The new ingredient is the passage from one minimal model to all of them. If the genus of `C` is
positive the minimal model is unique up to isomorphism over `R` ([Stacks, Tag 0C6B]). If the genus
is zero and some minimal model is not isomorphic to the given one, then the special fibre of every
minimal model is the projective line over the residue field ([Stacks, Tag 0CDA]), so every minimal
model is smooth over `R`, in particular at-worst-nodal.

## Main results

* `Stacks.Models.smooth_and_isAtWorstNodal_of_isProjectiveLineSpecialFiber` — a minimal model
  whose special fibre is the projective line is smooth and at-worst-nodal over `R`.
* `Stacks.Models.forall_of_exists_isMinimalModel` — a property of models which is invariant under
  isomorphism over `R` and holds for smooth minimal models passes from one minimal model to all.
* `Stacks.Models.tfae_hasSemistableReduction` — **Tag 0CDG.**
* `Stacks.Models.tfae_hasGoodReduction` — **Tag 0CDI.**

## References

* [Stacks Project, Tag 0CDG](https://stacks.math.columbia.edu/tag/0CDG)
* [Stacks Project, Tag 0CDI](https://stacks.math.columbia.edu/tag/0CDI)
* [Stacks Project, Tag 0C6B](https://stacks.math.columbia.edu/tag/0C6B)
* [Stacks Project, Tag 0CDA](https://stacks.math.columbia.edu/tag/0CDA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.ProjPolyChart (projToSpecCoeff)

universe u

namespace Stacks.Models

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- **A minimal model whose special fibre is the projective line is smooth and at-worst-nodal over
`R`.** The special fibre is smooth over the residue field, being isomorphic to `𝐏¹`, and so is
the generic fibre, the curve; a flat morphism of finite presentation with smooth fibres is smooth.
Nodality is the same fibrewise criterion with a smooth special fibre. -/
public theorem smooth_and_isAtWorstNodal_of_isProjectiveLineSpecialFiber {C X : Scheme.{u}}
    (c : C ⟶ Spec (.of K)) [IsCurve K c] [Smooth c] (p : X ⟶ Spec (.of R))
    (e : C ≅ pullback p (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hX : IsMinimalModel c p e) (h : IsProjectiveLineSpecialFiber p) :
    Smooth p ∧ IsAtWorstNodalOfRelativeDimensionOne p := by
  have := hX.isIso_globalSections
  have := hX.isProper
  obtain ⟨hflat, hlft, hqc, hce⟩ := hX.isModel
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  let S : RegularProperModelSituation.{u} :=
    { R := R, K := K, k := IsLocalRing.ResidueField R, residueEquiv := AlgEquiv.refl,
      C := C, C_to_K := c, X := X, X_to_R := p, flat := hflat,
      locallyOfFiniteType := hlft, quasiCompact := hqc, regular := hX.regular,
      genericFiberIso := e, genericFiberIso_over_K := hce,
      π := π, uniformizer := hπ, curveProjective := hX.curveProjective }
  obtain ⟨E, hE⟩ := h
  have : SmoothOfRelativeDimension 1 (projToSpecCoeff (IsLocalRing.ResidueField R) 1) :=
    Stacks.AlgebraicGeometry.ProjPolyChart.smoothOfRelativeDimension_projToSpecCoeff _ _
  have : Smooth (projToSpecCoeff (IsLocalRing.ResidueField R) 1) :=
    SmoothOfRelativeDimension.smooth 1 _
  have hsp : pullback.snd p (Spec.map (CommRingCat.ofHom
      (algebraMap R (IsLocalRing.ResidueField R)))) =
        E.inv ≫ projToSpecCoeff (IsLocalRing.ResidueField R) 1 := by
    rw [← hE, Iso.inv_hom_id_assoc]
  have hsm : Smooth S.specialFiberToSpec := by
    change Smooth (pullback.snd p (Spec.map (CommRingCat.ofHom
      (algebraMap R (IsLocalRing.ResidueField R)))))
    rw [hsp]
    infer_instance
  refine ⟨S.smooth_of_smooth_specialFiberToSpec hsm, ?_⟩
  let : S.specialFiber.Over (Spec (.of S.k)) := ⟨S.specialFiberToSpec⟩
  have : Smooth (S.specialFiber ↘ Spec (.of S.k)) := hsm
  exact S.isAtWorstNodalOfRelativeDimensionOne_of_specialFiber
    (Stacks.Curves.hasAtWorstNodalSingularities_of_smooth S.k S.specialFiber)

/-- **From one minimal model to all of them.** Let `P` be a property of models which is invariant
under isomorphism over `R` and holds for every smooth at-worst-nodal minimal model. If some
minimal model of `C` has `P`, then every minimal model has `P`: in positive genus two minimal
models are isomorphic over `R` ([Stacks, Tag 0C6B]); in genus zero either the given minimal model
is isomorphic to the one at hand, or there are two non-isomorphic minimal models and then every
minimal model has the projective line as special fibre ([Stacks, Tag 0CDA]), hence is smooth and
at-worst-nodal. -/
public theorem forall_of_exists_isMinimalModel {C : Scheme.{u}} (c : C ⟶ Spec (.of K))
    [IsCurve K c] [Smooth c] (hc : IsProjective c)
    [IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ c.appTop)]
    (P : ∀ {X : Scheme.{u}}, (X ⟶ Spec (.of R)) → Prop)
    (hiso : ∀ {X Y : Scheme.{u}} (φ : Y ≅ X) (p : X ⟶ Spec (.of R)), P p → P (φ.hom ≫ p))
    (hsmooth : ∀ {X : Scheme.{u}} (p : X ⟶ Spec (.of R)), Smooth p →
      IsAtWorstNodalOfRelativeDimensionOne p → P p)
    (h : ∃ (X : Scheme.{u}) (p : X ⟶ Spec (.of R))
      (e : C ≅ pullback p (Spec.map (CommRingCat.ofHom (algebraMap R K)))),
      IsMinimalModel c p e ∧ P p) :
    ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (.of R))
      (eY : C ≅ pullback q (Spec.map (CommRingCat.ofHom (algebraMap R K)))),
      IsMinimalModel c q eY → P q := by
  obtain ⟨X, p, e, hX, hP⟩ := h
  intro Y q eY hY
  rcases Nat.eq_zero_or_pos (genus c) with hg | hg
  · by_cases hex : ∃ φ : X ≅ Y, φ.hom ≫ q = p ∧
        e.hom ≫ pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≫ φ.hom =
          eY.hom ≫ pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap R K)))
    · obtain ⟨φ, hφ, -⟩ := hex
      have := hiso φ.symm p hP
      rwa [Iso.symm_hom, ← hφ, Iso.inv_hom_id_assoc] at this
    · have hP1 := isProjectiveLineSpecialFiber_of_isMinimalModel c
        ((isProjective_iff_isProjectiveMorphism_of_isAffine c).mp hc) inferInstance hg
        ⟨X, Y, p, q, e, eY, hX, hY, hex⟩ q eY hY
      obtain ⟨hs, hn⟩ := smooth_and_isAtWorstNodal_of_isProjectiveLineSpecialFiber c q eY hY hP1
      exact hsmooth q hs hn
  · obtain ⟨φ, hφ⟩ := exists_iso_comp_eq_of_isMinimalModel_of_pos_genus c hc hg p q e eY hX hY
    rw [← hφ]
    exact hiso φ p hP

/-- **Stacks Project, Tag 0CDG.** Let `R` be a discrete valuation ring with fraction field `K` and
let `C` be a smooth projective curve over `K` with `H⁰(C, 𝒪_C) = K`. The following are equivalent:
1. there exists a proper model of `C` which is at-worst-nodal of relative dimension one over `R`,
2. there exists a minimal model of `C` which is at-worst-nodal of relative dimension one over
   `R`, and
3. any minimal model of `C` is at-worst-nodal of relative dimension one over `R`.

Condition (1) is the base's `Stacks.Models.HasSemistableReduction`, the definition of semistable
reduction ([Stacks, Tag 0CDH]); minimal models are `Stacks.Models.IsMinimalModel`
([Stacks, Tag 0C2V]). -/
@[stacks 0CDG]
public theorem tfae_hasSemistableReduction {C : Scheme.{u}} (c : C ⟶ Spec (.of K))
    [IsCurve K c] [Smooth c] (hc : IsProjective c)
    [IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ c.appTop)] :
    List.TFAE [HasSemistableReduction R c hc,
      ∃ (X : Scheme.{u}) (p : X ⟶ Spec (.of R))
        (e : C ≅ pullback p (Spec.map (CommRingCat.ofHom (algebraMap R K)))),
        IsMinimalModel c p e ∧ IsAtWorstNodalOfRelativeDimensionOne p,
      ∀ (X : Scheme.{u}) (p : X ⟶ Spec (.of R))
        (e : C ≅ pullback p (Spec.map (CommRingCat.ofHom (algebraMap R K)))),
        IsMinimalModel c p e → IsAtWorstNodalOfRelativeDimensionOne p] := by
  tfae_have 1 → 2 := exists_isMinimalModel_isAtWorstNodal_of_hasSemistableReduction c hc
  tfae_have 2 → 1 := fun ⟨X, p, e, hX, hn⟩ ↦
    hasSemistableReduction_of_isMinimalModel_of_isAtWorstNodal c hc p e hX hn
  tfae_have 3 → 2 := exists_isMinimalModel_isAtWorstNodal_of_forall c hc
  tfae_have 2 → 3 := forall_of_exists_isMinimalModel c hc
    (fun p ↦ IsAtWorstNodalOfRelativeDimensionOne p)
    (fun φ p hp ↦ isAtWorstNodalOfRelativeDimensionOne_comp_etale p φ.hom hp)
    (fun _ _ hn ↦ hn)
  tfae_finish

/-- **Stacks Project, Tag 0CDI.** Let `R` be a discrete valuation ring with fraction field `K` and
let `C` be a smooth projective curve over `K` with `H⁰(C, 𝒪_C) = K`. The following are equivalent:
1. there exists a proper smooth model for `C`,
2. there exists a minimal model for `C` which is smooth over `R`,
3. any minimal model is smooth over `R`.

Condition (1) is the base's `Stacks.Models.HasGoodReduction`, the definition of good reduction
([Stacks, Tag 0CDJ]). A smooth proper model is minimal: its special fibre is connected
([Stacks, Tag 0C62]) and smooth, hence irreducible, so its numerical type is minimal
([Stacks, Tag 0CA6]). -/
@[stacks 0CDI]
public theorem tfae_hasGoodReduction {C : Scheme.{u}} (c : C ⟶ Spec (.of K))
    [IsCurve K c] [Smooth c] (hc : IsProjective c)
    [IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ c.appTop)] :
    List.TFAE [HasGoodReduction R c hc,
      ∃ (X : Scheme.{u}) (p : X ⟶ Spec (.of R))
        (e : C ≅ pullback p (Spec.map (CommRingCat.ofHom (algebraMap R K)))),
        IsMinimalModel c p e ∧ Smooth p,
      ∀ (X : Scheme.{u}) (p : X ⟶ Spec (.of R))
        (e : C ≅ pullback p (Spec.map (CommRingCat.ofHom (algebraMap R K)))),
        IsMinimalModel c p e → Smooth p] := by
  have hH : Stacks.HProjective.IsHProjective c :=
    (isProjective_iff_isProjectiveMorphism_of_isAffine c).mp hc
  tfae_have 1 → 2 := fun ⟨X, p, e, hmod, hprop, hsm⟩ ↦ by
    have := hprop
    have := hsm
    exact ⟨X, p, e, isMinimalModel_of_isModel_of_smooth c hH p e hmod, hsm⟩
  tfae_have 2 → 1 := fun ⟨X, p, e, hX, hsm⟩ ↦ ⟨X, p, e, hX.isModel, hX.isProper, hsm⟩
  tfae_have 3 → 2 := fun h ↦ by
    obtain ⟨X, p, e, hX⟩ := exists_isMinimalModel (R := R) c hH inferInstance
    exact ⟨X, p, e, hX, h X p e hX⟩
  tfae_have 2 → 3 := forall_of_exists_isMinimalModel c hc (fun p ↦ Smooth p)
    (fun φ p hp ↦ by have := hp; infer_instance) (fun _ hs _ ↦ hs)
  tfae_finish

end Stacks.Models

end
