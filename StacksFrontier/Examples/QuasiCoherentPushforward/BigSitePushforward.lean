module

public import Mathlib.Algebra.Polynomial.Cardinal
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModulePullbackBigSites
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.Examples.QuasiCoherentPushforward.BaseChangeFailure

/-!
# Stacks 03LC (2): `𝓕 ↦ 𝓕^a` is not compatible with pushforward over the big sites

Part (2) of [Stacks, Tag 03LC] says that the equivalences of Proposition 03DX part (1),
`QCoh(𝒪_S) ≃ QCoh((Sch/S)_τ, 𝒪)`, `𝓖 ↦ 𝓖^a`, are **not** compatible with pushforward in general.
For a morphism `f : X ⟶ Y` and a quasi-coherent `𝒪_X`-module `𝓕` the two candidates are the
pushforward `f_{big, *}(𝓕^a)` along the morphism of ringed big sites `f_big` of Stacks 070R (1),
whose sections over `T/Y` are the sections of `𝓕^a` over `X ×_Y T / X`, and the associated
module `(f_*𝓕)^a` of the ordinary direct image.  This file proves that they need not even be
isomorphic, for a quasi-compact and quasi-separated `f` (so that `f_*𝓕` is quasi-coherent and
`(f_*𝓕)^a` is an object of `QCoh((Sch/Y)_τ, 𝒪)`), on **every** big site and at **every**
`τ ∈ {Zariski, étale, smooth, syntomic, fppf}`.

The witness is the one of
`Stacks.Examples.QcohPushforward.exists_not_isIso_baseChangeNatTrans`
(`StacksFrontier/Examples/QuasiCoherentPushforward/BaseChangeFailure.lean`), the failure of base
change for `j : U = Spec A ∖ V(I) ⟶ Spec A` along `g : Spec (A/I) ⟶ Spec A`, which is the
source's explanation of the warning: compatibility over the big sites would mean that `f_*𝓕`
commutes with every base change.  The present file evaluates both sides at the object
`g : Spec (A/I) ⟶ Spec A` of the big site, using the two inputs of that failure:

* the fibre `U ×_{Spec A} Spec (A/I)` is empty
  (`Stacks.Examples.QcohPushforward.preimage_complementZeroLocus_eq_bot`), so
  `f_{big, *}(𝒪_U^a) = f_{big, *}𝒪` has zero sections over `g`;
* Hartogs, `A ≅ Γ(U, 𝒪_U)` (`Stacks.Examples.QcohPushforward.puncturedSectionsIso`), makes
  `j_*𝒪_U ≅ 𝒪_{Spec A}`, so `(j_*𝒪_U)^a ≅ 𝒪` has sections `Γ(Spec (A/I), 𝒪) = A/I ≠ 0` over `g`.

## Main results

* `Stacks.Examples.QcohPushforward.unitIsoPuncturedPushforward`: **Hartogs as an isomorphism
  of modules**, `𝒪_{Spec A} ≅ j_*𝒪_U`, when `I` is finitely generated and `A ⟶ Γ(U, 𝒪_U)` is
  bijective.
* `Stacks.Examples.QcohPushforward.isEmpty_iso_bigPushforward_associatedModule`: for every such
  `A`, `I` with `I ≠ ⊤`, every big site and every `τ`, there is no isomorphism
  `f_{big, *}(𝒪_U^a) ≅ (j_*𝒪_U)^a`.
* `Stacks.Examples.QcohPushforward.exists_isEmpty_iso_bigPushforward_associatedModule`:
  **Stacks 03LC part (2)**, with the concrete witness `k[t][X]`, `(X, t)`.

## Implementation notes

`𝒪^a = 𝒪` is `AlgebraicGeometry.BigFppfOver.isIso_basePullbackObjUnitToUnit`, and the sections
of the structure sheaf of a big site over an object are the global functions of its scheme on
the nose, so both evaluations are computed without any description of the sections of a general
associated module.

## References

* [Stacks Project, Tag 03LC](https://stacks.math.columbia.edu/tag/03LC)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.LocalCohomology Opposite

universe u

namespace Stacks.Examples.QcohPushforward

section General

variable (A : Type u) [CommRing A] (I : Ideal A)

/-- **Hartogs as an isomorphism of modules.**  For `I` finitely generated and
`A ⟶ Γ(U, 𝒪_U)` bijective, `j_*𝒪_U ≅ 𝒪_{Spec A}`: both are quasi-coherent on the affine scheme
`Spec A` (the first by Stacks 01LC, `j` being quasi-compact and quasi-separated), so both are the
tilde of their global sections, and those are `A` by
`Stacks.Examples.QcohPushforward.puncturedSectionsIso`. -/
def unitIsoPuncturedPushforward (hI : I.FG) (hb : Function.Bijective (complementTopScalars I)) :
    SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf ≅ puncturedPushforward A I :=
  tildeSelf.symm ≪≫ (tilde.functor (CommRingCat.of A)).mapIso (puncturedSectionsIso A I hb) ≪≫
    @asIso _ _ _ _ (Scheme.Modules.fromTildeΓ (R := CommRingCat.of A) (puncturedPushforward A I))
      ((isQuasicoherent_iff_isIso_fromTildeΓ _).mp (isQuasicoherent_puncturedPushforward A I hI))

variable (B : BigFppfSite.{u})

/-- `Spec (A/I)` lies in every big site containing `Spec A`, being a closed subscheme of it. -/
theorem contains_quotientSpec (hY : B.Contains (Spec (CommRingCat.of A))) :
    B.Contains (Spec (CommRingCat.of (A ⧸ I))) :=
  have : IsClosedImmersion (quotientSpecMap A I) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  Scheme.size_lt_of_isClosedImmersion (quotientSpecMap A I) hY

variable (hY : B.Contains (Spec (CommRingCat.of A)))

/-- `g : Spec (A/I) ⟶ Spec A` as an object of the big site over `Spec A`: the object over which
the two sides of the comparison are evaluated. -/
abbrev quotientObject : BigFppfOver B (Spec (CommRingCat.of A)) hY :=
  Over.mk (ObjectProperty.homMk (X := B.obj (contains_quotientSpec A I B hY))
    (quotientSpecMap A I))

/-- **The fibre of `U` over `Spec (A/I)`, as the object of the big site of `U` that `f_big`
assigns to `g`, is empty.**  A point of `U ×_{Spec A} Spec (A/I)` would map to a point of
`Spec (A/I)` whose image lies in `U`, and there is none
(`Stacks.Examples.QcohPushforward.preimage_complementZeroLocus_eq_bot`). -/
theorem isEmpty_baseChange_quotientObject (hX : B.Contains (puncturedScheme A I)) :
    IsEmpty (B.inclusion.obj ((BigFppfOver.baseChange B hX hY
      (complementZeroLocus A I).ι).obj (quotientObject A I B hY)).left) := by
  change IsEmpty (B.inclusion.obj (pullback (quotientObject A I B hY).hom
    (BigFppfOver.siteHom B hX hY (complementZeroLocus A I).ι)))
  refine ⟨fun p => ?_⟩
  have hc := congrArg B.inclusion.map (pullback.condition (f := (quotientObject A I B hY).hom)
      (g := BigFppfOver.siteHom B hX hY (complementZeroLocus A I).ι))
  rw [Functor.map_comp, Functor.map_comp] at hc
  have h := congrArg (fun k => k p) hc
  simp only [Scheme.Hom.comp_apply] at h
  have hmem : (B.inclusion.map (pullback.fst (quotientObject A I B hY).hom
      (BigFppfOver.siteHom B hX hY (complementZeroLocus A I).ι))) p ∈
      (quotientSpecMap A I ⁻¹ᵁ complementZeroLocus A I) := by
    change (B.inclusion.map (quotientObject A I B hY).hom) _ ∈
      ((complementZeroLocus A I : (Spec (CommRingCat.of A)).Opens) : Set (Spec (CommRingCat.of A)))
    rw [h]
    exact Scheme.Opens.range_ι (complementZeroLocus A I) ▸ Set.mem_range_self _
  rwa [preimage_complementZeroLocus_eq_bot A I] at hmem

variable (hX : B.Contains (puncturedScheme A I)) (τ : SiteKind)

/-- **`f_{big, *}𝒪` has zero sections over `g`**: they are the global functions of the empty
scheme `U ×_{Spec A} Spec (A/I)`. -/
theorem subsingleton_bigPushforward_unit_sections :
    Subsingleton ((_root_.SheafOfModules.evaluation
      (FibredSite.baseRingStructureSheaf B (Spec (CommRingCat.of A)) hY τ)
        (op (quotientObject A I B hY))).obj
      ((SheafOfModules.pushforward.{u}
        (BigFppfOver.baseStructureComparison B hX hY (complementZeroLocus A I).ι τ)).obj
        (SheafOfModules.unit
          (FibredSite.baseRingStructureSheaf B (puncturedScheme A I) hX τ)))) := by
  have := isEmpty_baseChange_quotientObject A I B hY hX
  change Subsingleton Γ(B.inclusion.obj ((BigFppfOver.baseChange B hX hY
    (complementZeroLocus A I).ι).obj (quotientObject A I B hY)).left, ⊤)
  have htop : (⊤ : (B.inclusion.obj ((BigFppfOver.baseChange B hX hY
      (complementZeroLocus A I).ι).obj (quotientObject A I B hY)).left).Opens) = ⊥ := by
    ext x
    exact isEmptyElim x
  rw [htop]
  infer_instance

/-- **`𝒪` has nonzero sections over `g`**: they are `Γ(Spec (A/I), 𝒪) = A/I`, nonzero because
`I` is proper. -/
theorem nontrivial_bigUnit_sections (hIne : I ≠ ⊤) :
    Nontrivial ((_root_.SheafOfModules.evaluation
      (FibredSite.baseRingStructureSheaf B (Spec (CommRingCat.of A)) hY τ)
        (op (quotientObject A I B hY))).obj
      (SheafOfModules.unit
        (FibredSite.baseRingStructureSheaf B (Spec (CommRingCat.of A)) hY τ))) := by
  have : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hIne
  change Nontrivial Γ(Spec (CommRingCat.of (A ⧸ I)), ⊤)
  exact (Scheme.ΓSpecIso (CommRingCat.of (A ⧸ I))).commRingCatIsoToRingEquiv.toEquiv.nontrivial

/-- **`f_{big, *}(𝓕^a)` and `(f_*𝓕)^a` differ**, for `j : U = Spec A ∖ V(I) ⟶ Spec A` and
`𝓕 = 𝒪_U`, whenever `I` is finitely generated and proper and `A ⟶ Γ(U, 𝒪_U)` is bijective: on
every big site and at every `τ`, the two `𝒪`-modules on `(Sch/Spec A)_τ` are not isomorphic.

An isomorphism would give, through `𝒪_U^a ≅ 𝒪`, Hartogs `j_*𝒪_U ≅ 𝒪_{Spec A}` and
`𝒪_{Spec A}^a ≅ 𝒪`, an isomorphism `f_{big, *}𝒪 ≅ 𝒪`, hence a bijection between their sections
over `g : Spec (A/I) ⟶ Spec A`; the first are zero and the second are `A/I ≠ 0`. -/
theorem isEmpty_iso_bigPushforward_associatedModule (hI : I.FG) (hIne : I ≠ ⊤)
    (hb : Function.Bijective (complementTopScalars I)) :
    IsEmpty ((SheafOfModules.pushforward.{u}
        (BigFppfOver.baseStructureComparison B hX hY (complementZeroLocus A I).ι τ)).obj
        ((BigFppfOver.baseAssociatedModule B (puncturedScheme A I) hX τ).obj (puncturedUnit A I)) ≅
      (BigFppfOver.baseAssociatedModule B (Spec (CommRingCat.of A)) hY τ).obj
        (puncturedPushforward A I)) := by
  refine ⟨fun e => ?_⟩
  let E := (SheafOfModules.pushforward.{u}
      (BigFppfOver.baseStructureComparison B hX hY (complementZeroLocus A I).ι τ)).mapIso
      (@asIso _ _ _ _ (SheafOfModules.pullbackObjUnitToUnit.{u}
        (BigFppfOver.baseStructureMap B (puncturedScheme A I) hX τ))
        (BigFppfOver.isIso_basePullbackObjUnitToUnit B (puncturedScheme A I) hX τ)).symm ≪≫ e ≪≫
    (BigFppfOver.baseAssociatedModule B (Spec (CommRingCat.of A)) hY τ).mapIso
      (unitIsoPuncturedPushforward A I hI hb).symm ≪≫
    @asIso _ _ _ _ (SheafOfModules.pullbackObjUnitToUnit.{u}
        (BigFppfOver.baseStructureMap B (Spec (CommRingCat.of A)) hY τ))
      (BigFppfOver.isIso_basePullbackObjUnitToUnit B (Spec (CommRingCat.of A)) hY τ)
  let E' := (_root_.SheafOfModules.evaluation
    (FibredSite.baseRingStructureSheaf B (Spec (CommRingCat.of A)) hY τ)
      (op (quotientObject A I B hY))).mapIso E
  have := subsingleton_bigPushforward_unit_sections A I B hY hX τ
  have := nontrivial_bigUnit_sections A I B hY τ hIne
  exact not_subsingleton _ E'.toLinearEquiv.toEquiv.symm.subsingleton

end General

/-! ### The concrete witness lies in every big site -/

/-- The ring `k[t][X]` of the counterexample is countable. -/
theorem mk_counterexampleRing_le : Cardinal.mk counterexampleRing.{u} ≤ Cardinal.aleph0 := by
  have hk : Cardinal.mk counterexampleField.{u} ≤ Cardinal.aleph0 := by
    simp [counterexampleField]
  refine Polynomial.cardinalMk_le_max.trans (max_le ?_ le_rfl)
  exact Polynomial.cardinalMk_le_max.trans (max_le hk le_rfl)

/-- `Spec k[t][X]` lies in every big fppf site: its size is `ℵ₀`, below every cutoff. -/
theorem contains_spec_counterexampleRing (B : BigFppfSite.{u}) :
    B.Contains (Spec (CommRingCat.of counterexampleRing.{u})) := by
  rw [BigFppfSite.Contains, Scheme.size_Spec]
  exact max_lt B.aleph0_lt_cutoff (mk_counterexampleRing_le.trans_lt B.aleph0_lt_cutoff)

/-! ### Stacks 03LC part (2) -/

/-- **Stacks Project, Tag 03LC part (2).**  The equivalences `𝓖 ↦ 𝓖^a` of Proposition 03DX part
(1) are **not** compatible with pushforward in general: there are a morphism of schemes
`f : X ⟶ Y`, quasi-compact and quasi-separated, and a quasi-coherent `𝒪_X`-module `𝓕` — so
that `f_*𝓕` is quasi-coherent and `(f_*𝓕)^a` is defined — such that on every big site (both
schemes lie in every one) and at every `τ ∈ {Zariski, étale, smooth, syntomic, fppf}`

    `f_{big, *}(𝓕^a) ≇ (f_*𝓕)^a`

as `𝒪`-modules on `(Sch/Y)_τ`, where `f_{big, *}` is the pushforward along the morphism of
ringed big sites `f_big : ((Sch/X)_τ, 𝒪) ⟶ ((Sch/Y)_τ, 𝒪)` of Stacks 070R (1).

The witness is the source's: the punctured plane `U = Spec k[t][X] ∖ V(X, t)` over
`Spec k[t][X]`, with `k = ULift ℚ`, and `𝓕 = 𝒪_U`; the two sides differ over the origin
`Spec k ⟶ Spec k[t][X]`, which is where the base-change map of
`Stacks.Examples.QcohPushforward.exists_not_isIso_baseChangeNatTrans` fails. -/
@[stacks 03LC "(2)"]
theorem exists_isEmpty_iso_bigPushforward_associatedModule :
    ∃ (X Y : Scheme.{u}) (f : X ⟶ Y) (F : X.Modules),
      QuasiCompact f ∧ QuasiSeparated f ∧ F.IsQuasicoherent ∧
        ((Scheme.Modules.pushforward f).obj F).IsQuasicoherent ∧
        (∀ B : BigFppfSite.{u}, B.Contains X ∧ B.Contains Y) ∧
        ∀ (B : BigFppfSite.{u}) (hX : B.Contains X) (hY : B.Contains Y) (τ : SiteKind),
          IsEmpty ((SheafOfModules.pushforward.{u}
              (BigFppfOver.baseStructureComparison B hX hY f τ)).obj
              ((BigFppfOver.baseAssociatedModule B X hX τ).obj F) ≅
            (BigFppfOver.baseAssociatedModule B Y hY τ).obj
              ((Scheme.Modules.pushforward f).obj F)) :=
  ⟨puncturedScheme counterexampleRing.{u} counterexampleIdeal.{u},
    Spec (CommRingCat.of counterexampleRing.{u}),
    (complementZeroLocus counterexampleRing.{u} counterexampleIdeal.{u}).ι,
    puncturedUnit counterexampleRing.{u} counterexampleIdeal.{u},
    quasiCompact_punctured_ι _ _ counterexampleIdeal_fg, inferInstance, inferInstance,
    isQuasicoherent_puncturedPushforward _ _ counterexampleIdeal_fg,
    fun B => ⟨BigFppfOver.contains_opens B (contains_spec_counterexampleRing B) _,
      contains_spec_counterexampleRing B⟩,
    fun B hX hY τ => isEmpty_iso_bigPushforward_associatedModule _ _ B hY hX τ
      counterexampleIdeal_fg counterexampleIdeal_ne_top
      bijective_complementTopScalars_counterexample⟩

end Stacks.Examples.QcohPushforward

end
