module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.StrictHenselizationSections
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The stalk of a direct image as sections over the strict henselization

Let `φ : A ⟶ S` be quasi-compact and quasi-separated, `s` a geometric point of `S` and
`π : Spec 𝒪^{sh}_{S,s} ⟶ S` the strict henselization at `s`. For a sheaf of sets `F` on the small
étale site of `A`, the stalk of the direct image is
```
(φ_* F)_s ≅ Γ(A ×_S Spec 𝒪^{sh}_{S,s}, p⁻¹ F),
```
with `p : A ×_S Spec 𝒪^{sh}_{S,s} ⟶ A` the projection. The stalk at `s` is the stalk at the
canonical lift `s̃` of the pullback along `π`, which is global sections over the strictly
henselian `Spec 𝒪^{sh}_{S,s}` because `s̃` lies over its closed point; the base change map
`π⁻¹ φ_* F ⟶ (φ_π)_* p⁻¹ F` is bijective on global sections (Stacks 03Q9 in degree zero,
`Stacks.EtaleCohomology.isIso_Γ_map_smallEtaleSetBaseChange_strictHenselization`); and global
sections of a direct image are global sections of the sheaf.

This is the first half of the identification of the local invariants `H⁰_loc` of Weil II 1.8: for
an open immersion `j : U ⟶ X̄` of curves and a point `y` of the boundary, the stalk of `j_* F` at
`ȳ` is the set of sections of `F` over `U ×_X̄ Spec 𝒪^{sh}_{X̄,ȳ}`, the spectrum of the fraction
field of the strictly henselian discrete valuation ring `𝒪^{sh}_{X̄,ȳ}`.

## Main definitions

* `Stacks.EtaleCohomology.stalkIsoStrictHenselizationGamma` — the stalk of a sheaf of sets at
  `s` is the set of global sections of its pullback to the strict henselization.

## Main results

* `Stacks.EtaleCohomology.nonempty_directImageStalkIsoStrictHenselizationGamma` — the stalk of
  `φ_* F` at `s` is isomorphic to `Γ(A ×_S Spec 𝒪^{sh}_{S,s}, p⁻¹ F)`.

## Implementation notes

The second identification is stated as `Nonempty` of an isomorphism: packaged as a definition, the
composite (whose middle factor is `asIso` of the base change map) makes the kernel time out.

## References

* [Stacks Project, Tag 03Q9](https://stacks.math.columbia.edu/tag/03Q9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)

/-- **The stalk at a geometric point is the set of sections over the strict henselization.**
The stalk at `s` is the stalk at the canonical lift `s̃` of the pullback along
`π : Spec 𝒪^{sh}_{S,s} ⟶ S`, and over the strictly henselian local ring the stalk at a point
above the closed point is the set of global sections. -/
@[sga "4 VIII 4.8"]
def stalkIsoStrictHenselizationGamma :
    (pointSmallEtale s.hom).sheafFiber (A := Type (u + 1)) ≅
      smallEtaleInverseImage.{u, 0} (strictHenselizationToBase B S hS s) ⋙
        Sheaf.Γ (strictHenselization B S hS s).smallEtaleTopology (Type (u + 1)) :=
  eqToIso (congrArg (fun y : s.source ⟶ S ↦ (pointSmallEtale y).sheafFiber (A := Type (u + 1)))
      (geometricPointToStrictHenselization_comp B S hS s).symm) ≪≫
    (smallEtaleInverseImageStalkIso.{0, u} (strictHenselizationToBase B S hS s)
      (geometricPointToStrictHenselization B S hS s)).symm ≪≫
    Functor.isoWhiskerLeft (smallEtaleInverseImage.{u, 0} (strictHenselizationToBase B S hS s))
      (sheafFiberClosedPointIsoGamma.{u, 0} (geometricPointToStrictHenselization B S hS s)
        (geometricPointToStrictHenselization_base_default B S hS s))

variable {A : Scheme.{u}} (φ : A ⟶ S) [QuasiCompact φ] [QuasiSeparated φ]
  (F : Sheaf A.smallEtaleTopology (Type (u + 1)))

/-- **The stalk of a direct image at a geometric point** (Stacks 03Q9 in degree zero, sets). For
`φ : A ⟶ S` quasi-compact and quasi-separated and a sheaf of sets `F` on the small étale site of
`A`, the stalk of `φ_* F` at `s` is the set of sections of `p⁻¹ F` over
`A ×_S Spec 𝒪^{sh}_{S,s}`. -/
theorem nonempty_directImageStalkIsoStrictHenselizationGamma :
    Nonempty ((pointSmallEtale s.hom).sheafFiber.obj
        (((smallEtaleBaseChange φ).sheafPushforwardContinuous (Type (u + 1))
          (smallEtaleTopology S) (smallEtaleTopology A)).obj F) ≅
      (Sheaf.Γ (pullback φ (strictHenselizationToBase B S hS s)).smallEtaleTopology
        (Type (u + 1))).obj
        ((smallEtaleInverseImage.{u, 0} (pullback.fst φ (strictHenselizationToBase B S hS s))).obj
          F)) :=
  ⟨(stalkIsoStrictHenselizationGamma B S hS s).app _ ≪≫
    @asIso _ _ _ _ _ (isIso_Γ_map_smallEtaleSetBaseChange_strictHenselization B S hS s φ F) ≪≫
    (smallEtalePushforwardGammaIso.{u, 0} (pullback.snd φ (strictHenselizationToBase B S hS s))).app
      _⟩

end Stacks.EtaleCohomology
