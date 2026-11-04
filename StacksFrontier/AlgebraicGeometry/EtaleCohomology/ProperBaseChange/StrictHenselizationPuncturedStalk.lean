module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.StrictHenselizationDirectImageStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.StrictHenselizationDiscreteValuation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.PuncturedDiscreteValuationSpectrum

/-!
# The stalk of `j_* F` at a boundary point of a curve

Let `S` be an irreducible scheme, `s` a geometric point of `S` over a point `x` whose local ring
`𝒪_{S,x}` is a noetherian discrete valuation ring (a closed point of a regular curve), and let
`j : U ⟶ S` be a quasi-compact open immersion with `U` nonempty and `x ∉ U`. Then the strict
henselization `𝒪^{sh}_{S,s}` is a discrete valuation ring with uniformizer `ϖ`, the generic point
of its spectrum lies over `U` and its closed point over `x`, so `U ×_S Spec 𝒪^{sh}_{S,s}` is
`Spec 𝒪^{sh}_{S,s}[1/ϖ] = Spec K^{sh}`, and for a sheaf of sets `F` on `U`
```
(j_* F)_s ≅ Γ(Spec K^{sh}, F|),
```
the sections of the pullback of `F` to the spectrum of the fraction field of the strict
henselization. This is the identification of the local invariants `H⁰_loc` at a boundary point
(Weil II 1.8) with the sections over `Spec K^{sh}`, which Stacks 04JM turns into the invariants of
the inertia group.

## Main results

* `Stacks.EtaleCohomology.exists_directImageStalkIso_localizationAway` — the displayed
  identification.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme IsLocalRing

universe u

namespace Stacks.EtaleCohomology

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)

/-- The strict henselization sends its closed point to the image of the geometric point. -/
alias strictHenselizationToBase_closedPoint :=
  AlgebraicGeometry.strictHenselizationToBase_closedPoint

/-- **The stalk of `j_* F` at a boundary point is the set of sections over `Spec K^{sh}`.** -/
theorem exists_directImageStalkIso_localizationAway [IrreducibleSpace S]
    [IsNoetherianRing ↥(S.presheaf.stalk (s.hom (closedPoint s.residueField)))]
    [IsDomain ↥(S.presheaf.stalk (s.hom (closedPoint s.residueField)))]
    [IsDiscreteValuationRing ↥(S.presheaf.stalk (s.hom (closedPoint s.residueField)))]
    {U : Scheme.{u}} (j : U ⟶ S) [IsOpenImmersion j] [QuasiCompact j] [Nonempty U]
    (hx : s.hom (closedPoint s.residueField) ∉ Set.range j)
    (F : Sheaf U.smallEtaleTopology (Type (u + 1))) :
    ∃ (ϖ : ↥(etaleLocalRing B S hS s)) (_ : Irreducible ϖ)
      (e : pullback j (strictHenselizationToBase B S hS s) ≅
        Spec (.of (Localization.Away ϖ))),
      e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap _ (Localization.Away ϖ))) =
          pullback.snd j (strictHenselizationToBase B S hS s) ∧
        Nonempty ((pointSmallEtale s.hom).sheafFiber.obj
            (((smallEtaleBaseChange j).sheafPushforwardContinuous (Type (u + 1))
              (smallEtaleTopology S) (smallEtaleTopology U)).obj F) ≅
          (Sheaf.Γ (Spec (.of (Localization.Away ϖ))).smallEtaleTopology (Type (u + 1))).obj
            (((smallEtaleBaseChange e.hom).sheafPushforwardContinuous (Type (u + 1))
              (smallEtaleTopology (Spec (.of (Localization.Away ϖ))))
              (smallEtaleTopology (pullback j (strictHenselizationToBase B S hS s)))).obj
              ((smallEtaleInverseImage.{u, 0}
                (pullback.fst j (strictHenselizationToBase B S hS s))).obj F))) := by
  obtain ⟨hdom, hdvr⟩ := isDomain_and_isDiscreteValuationRing_etaleLocalRing B S hS s
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible ↥(etaleLocalRing B S hS s)
  have hgen := strictHenselizationToBase_bot_mem B S hS s j.opensRange
    (by obtain ⟨u⟩ := ‹Nonempty U›; exact ⟨j u, u, rfl⟩)
  obtain ⟨e, he⟩ := exists_pullback_iso_spec_away_of_isDiscreteValuationRing
    ↥(etaleLocalRing B S hS s) hϖ j (strictHenselizationToBase B S hS s) hgen
    (by rw [strictHenselizationToBase_closedPoint]; exact hx)
  obtain ⟨i⟩ := nonempty_directImageStalkIsoStrictHenselizationGamma B S hS s j F
  exact ⟨ϖ, hϖ, e, he, ⟨i ≪≫
    ((smallEtalePushforwardGammaIso.{u, 0} e.hom).app _).symm⟩⟩

end Stacks.EtaleCohomology
