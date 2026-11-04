module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalConnectionCrisIntegrable
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalIntegrableConnection

/-!
# A crystal in `𝒪_{X/S}`-modules on `Cris(X/S)` has a canonical integrable connection

This is [Stacks, Lemma 60.15.1, Tag 07J6]: in Situation 07MF, let `F` be a crystal in
`𝒪_{X/S}`-modules on the small crystalline site `Cris(X/S)`; then `F` comes equipped with a
canonical integrable connection.

[Stacks, Section 60.15, Tag 07J5] defines a connection on a sheaf `F` of `𝒪_{X/S}`-modules as a
map of abelian sheaves `∇ : F ⟶ F ⊗_{𝒪_{X/S}} Ω_{X/S}` with `∇(f s) = f ∇(s) + s ⊗ d f`, its
extensions `F ⊗ Ω^i_{X/S} ⟶ F ⊗ Ω^{i+1}_{X/S}` by `∇(s ⊗ ω) = ∇(s) ∧ ω + s ⊗ d ω`, and calls it
integrable when `∇ ∘ ∇ = 0`.  Throughout, `F` is a crystal (`...SmallSite.IsSheafCrystal`); no
quasi-coherence is assumed.

The canonical connection is `...SmallSite.crystalConnectionCris`, a morphism of abelian sheaves
`∇ : F ⟶ F ⊗_{𝒪_{X/S}} Ω_{X/S}` on `Cris(X/S)`.  Here `F ⊗ Ω_{X/S}` is
`...SmallSite.tensorDifferentialFormsSheaf F 1`, the sheafification of `A ↦ F(A) ⊗ Ω_{X/S}(A)`.
On the ambient scheme `T` of every object it is `s ↦ p₁^* s - p₀^* s` on the first-order
universal thickening `T'` of [Stacks, Tag 07J2], read in `F_T ⊗ Ω_{T/S,δ} ⊂ F_{T'}`, through the
identification `(F ⊗ Ω_{X/S})_T = F_T ⊗_{𝒪_T} Ω_{T/S,δ}` of `...SmallSite.tensorFormsAmbientIso`
([Stacks, Tag 07IZ] carried through the tensor product).

## Main results

* `crystalConnectionCris_isConnection` — **it is a connection**: the Leibniz rule
  `∇(f s) = f ∇(s) + s ⊗ d f` for all local sections, the scalars on `F ⊗ Ω_{X/S}` being those
  of the sheaf of `𝒪_{X/S}`-modules `...SmallSite.tensorDifferentialFormsModuleSheaf`; and the
  description of `∇` on each `T` as `p₁^* s - p₀^* s`.
* `crystalConnectionCris_isIntegrable` — **it is integrable**: the extension
  `...SmallSite.crystalExtensionCris : F ⊗ Ω_{X/S} ⟶ F ⊗ Ω²_{X/S}`, a morphism of abelian
  sheaves, is given by the rule `∇(s ⊗ ω) = ∇(s) ∧ ω + s ⊗ d ω` on local pure tensors
  (which determines it: `...SmallSite.eq_crystalExtensionCris`), the exterior product being
  `(x ⊗ η) ∧ ω = x ⊗ (η ∧ ω)`, and `∇ ∘ ∇ = 0`.
* `crystalConnectionCris_isIntegrableConnection` — **the lemma as a whole**: the conjunction of
  the two previous statements, that `crystalConnectionCris` is a canonical integrable connection.

## References

* [Stacks Project, Tag 07J6](https://stacks.math.columbia.edu/tag/07J6)
* [Stacks Project, Tag 07J5](https://stacks.math.columbia.edu/tag/07J5)
* [Stacks Project, Tag 07I0](https://stacks.math.columbia.edu/tag/07I0)
* [Stacks Project, Tag 07IZ](https://stacks.math.columbia.edu/tag/07IZ)
* [Stacks Project, Tag 07J2](https://stacks.math.columbia.edu/tag/07J2)
* [Stacks Project, Tag 07J3](https://stacks.math.columbia.edu/tag/07J3)
* [Stacks Project, Tag 07MF](https://stacks.math.columbia.edu/tag/07MF)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

attribute [local instance] moduleCrysFormRingSections moduleTensorFormsModSec

variable {S : GlobalCrystallineSituation.{u}} {F : SheafOfModules.{u} (structureSheaf S)}

/-- **The canonical connection of a crystal is a connection on `Cris(X/S)`** (the first half of
[Stacks, Lemma 60.15.1, Tag 07J6]).
Let `F` be a crystal in `𝒪_{X/S}`-modules on `Cris(X/S)` and
`∇ = crystalConnectionCris : F ⟶ F ⊗_{𝒪_{X/S}} Ω_{X/S}` its canonical connection, a morphism of
abelian sheaves on `Cris(X/S)`.  Then

1. (**Leibniz rule**) for every object `A`, every section `f` of `𝒪_{X/S}` and every section `s`
   of `F` over `A`, `∇(f s) = f ∇(s) + s ⊗ d f`;
2. (**the canonical connection**) on the ambient scheme `T` of every object, `∇(s)` is
   `p₁^* s - p₀^* s` on the first-order universal thickening `T'` of [Stacks, Tag 07J2]: read in
   `F_T ⊗ Ω_{T/S,δ}` through `(F ⊗ Ω_{X/S})_T = F_T ⊗ Ω_{T/S,δ}` and then in `F_{T'}`, it is the
   difference of the two pullbacks. -/
theorem crystalConnectionCris_isConnection (hF : IsSheafCrystal F) :
    (∀ (A : CrystallineThickening S) (f : crysFormRing S A) (s : F.val.obj (op A)),
      (show tensorFormsModSec F 1 A from
        (crystalConnectionCris hF).hom.app (op A) (ULift.up (f • s))) =
        f • (show tensorFormsModSec F 1 A from
          (crystalConnectionCris hF).hom.app (op A) (ULift.up s)) +
        (show tensorFormsModSec F 1 A from
          (CategoryTheory.toSheafify (smallTopology S) (tensorDifferentialFormsPresheaf F 1)).app
            (op A) (ULift.up (formsTmul F s (formsD A f))))) ∧
    ∀ (A : CrystallineThickening S) (s : (abelianSheaf F).obj.obj (op A)),
      (firstOrderTensorInclusion F A).val.app (op ⊤)
          ((tensorFormsAmbientIsoOne A).hom.app (op ⊤)
            ((tensorDifferentialFormsSheaf F 1).obj.map (A.restrictOpenHom ⊤).op
              ((crystalConnectionCris hF).hom.app (op A) s))).down =
        crystalConnectionRaw F A ⊤ (F.val.map (A.restrictOpenHom ⊤).op s.down) := by
  refine ⟨fun A f s ↦ ?_, fun A s ↦ ?_⟩
  · rw [crystalConnectionCris_app]
    exact crystalConnectionCris_smul hF A f s
  · rw [crystalConnectionCris_app, tensorFormsAmbientIsoOne_hom_restrict_crystalConnectionCrisApp]
    exact firstOrderTensorInclusion_crystalConnectionApp A hF ⊤ _

/-- **The canonical connection of a crystal is integrable** (the second half of
[Stacks, Lemma 60.15.1, Tag 07J6]).  Let `F` be a crystal in `𝒪_{X/S}`-modules on `Cris(X/S)`
with its canonical connection `∇ = crystalConnectionCris`, and let
`∇ = crystalExtensionCris : F ⊗ Ω_{X/S} ⟶ F ⊗ Ω²_{X/S}` be its extension, a morphism of abelian
sheaves on `Cris(X/S)`.  Then

1. the exterior product `z ↦ z ∧ ω` by a section `ω` of `Ω_{X/S}` is
   `(x ⊗ η) ∧ ω = x ⊗ (η ∧ ω)` on local pure tensors;
2. (**the rule of [Stacks, Tag 07I0]**) `∇(s ⊗ ω) = ∇(s) ∧ ω + s ⊗ d ω` for every object and
   all sections `s` of `F` and `ω` of `Ω_{X/S}` there — which determines the extension
   (`...SmallSite.eq_crystalExtensionCris`);
3. (**integrability**) `∇ ∘ ∇ = 0 : F ⟶ F ⊗ Ω²_{X/S}`. -/
theorem crystalConnectionCris_isIntegrable (hF : IsSheafCrystal F) :
    (∀ (A : CrystallineThickening S) (ω : (crysDifferentialForms S 1).obj (op A))
        (x : F.val.obj (op A)) (η : (crysDifferentialForms S 1).obj (op A)),
      crystalWedgeCrisApp F A ω
          ((CategoryTheory.toSheafify (smallTopology S) (tensorDifferentialFormsPresheaf F 1)).app
            (op A) (ULift.up (formsTmul F x η))) =
        (CategoryTheory.toSheafify (smallTopology S) (tensorDifferentialFormsPresheaf F 2)).app
          (op A) (ULift.up (formsTmul F x (formsWedgeOne η ω)))) ∧
    (∀ (A : CrystallineThickening S) (s : F.val.obj (op A))
        (ω : (crysDifferentialForms S 1).obj (op A)),
      (crystalExtensionCris hF).hom.app (op A)
          ((CategoryTheory.toSheafify (smallTopology S) (tensorDifferentialFormsPresheaf F 1)).app
            (op A) (ULift.up (formsTmul F s ω))) =
        crystalWedgeCrisApp F A ω ((crystalConnectionCris hF).hom.app (op A) (ULift.up s)) +
          (show (tensorDifferentialFormsSheaf F 2).obj.obj (op A) from
            (CategoryTheory.toSheafify (smallTopology S) (tensorDifferentialFormsPresheaf F 2)).app
              (op A) (ULift.up (formsTmul F s (formsDeRham A ω))))) ∧
    crystalConnectionCris hF ≫ crystalExtensionCris hF = 0 := by
  refine ⟨fun A ω x η ↦ crystalWedgeCrisApp_toSheafify A ω x η, fun A s ω ↦ ?_,
    crystalConnectionCris_comp_crystalExtensionCris hF⟩
  rw [crystalExtensionCris_app, crystalConnectionCris_app]
  exact crystalExtensionCrisApp_toSheafify hF A s ω

/-- **A crystal `F` in `𝒪_{X/S}`-modules on `Cris(X/S)` comes equipped with a canonical integrable
connection.**  The connection is
`∇ = crystalConnectionCris : F ⟶ F ⊗_{𝒪_{X/S}} Ω_{X/S}`, a morphism of abelian sheaves on
`Cris(X/S)`, and

1. (**it is a connection**) `∇(f s) = f ∇(s) + s ⊗ d f` for every object `A` and all sections `f`
   of `𝒪_{X/S}` and `s` of `F` over `A`;
2. (**it is the canonical one**) on the ambient scheme `T` of every object, `∇(s)` is
   `p₁^* s - p₀^* s` on the first-order thickening `T'` of [Stacks, Tag 07J2], read in
   `F_T ⊗ Ω_{T/S,δ} ⊂ F_{T'}`;
3. the exterior product by a one-form is `(x ⊗ η) ∧ ω = x ⊗ (η ∧ ω)` on local pure tensors, and
   the extension `crystalExtensionCris : F ⊗ Ω_{X/S} ⟶ F ⊗ Ω²_{X/S}` is given by the rule
   `∇(s ⊗ ω) = ∇(s) ∧ ω + s ⊗ d ω` of [Stacks, Tag 07I0] and [Stacks, Section 60.15, Tag 07J5];
4. (**it is integrable**) `∇ ∘ ∇ = 0 : F ⟶ F ⊗ Ω²_{X/S}`. -/
@[stacks 07J6 "a crystal F on Cris(X/S) has a canonical integrable connection: \
∇ = crystalConnectionCris : F ⟶ F ⊗ Ω_{X/S}, a morphism of abelian sheaves, satisfies the \
Leibniz rule, is p₁^* s - p₀^* s on every T, its extension F ⊗ Ω ⟶ F ⊗ Ω² obeys \
∇(s ⊗ ω) = ∇(s) ∧ ω + s ⊗ d ω, and ∇ ∘ ∇ = 0"]
theorem crystalConnectionCris_isIntegrableConnection (hF : IsSheafCrystal F) :
    ((∀ (A : CrystallineThickening S) (f : crysFormRing S A) (s : F.val.obj (op A)),
        (show tensorFormsModSec F 1 A from
          (crystalConnectionCris hF).hom.app (op A) (ULift.up (f • s))) =
          f • (show tensorFormsModSec F 1 A from
            (crystalConnectionCris hF).hom.app (op A) (ULift.up s)) +
          (show tensorFormsModSec F 1 A from
            (CategoryTheory.toSheafify (smallTopology S) (tensorDifferentialFormsPresheaf F 1)).app
              (op A) (ULift.up (formsTmul F s (formsD A f))))) ∧
      ∀ (A : CrystallineThickening S) (s : (abelianSheaf F).obj.obj (op A)),
        (firstOrderTensorInclusion F A).val.app (op ⊤)
            ((tensorFormsAmbientIsoOne A).hom.app (op ⊤)
              ((tensorDifferentialFormsSheaf F 1).obj.map (A.restrictOpenHom ⊤).op
                ((crystalConnectionCris hF).hom.app (op A) s))).down =
          crystalConnectionRaw F A ⊤ (F.val.map (A.restrictOpenHom ⊤).op s.down)) ∧
    ((∀ (A : CrystallineThickening S) (ω : (crysDifferentialForms S 1).obj (op A))
          (x : F.val.obj (op A)) (η : (crysDifferentialForms S 1).obj (op A)),
        crystalWedgeCrisApp F A ω
            ((CategoryTheory.toSheafify (smallTopology S) (tensorDifferentialFormsPresheaf F 1)).app
              (op A) (ULift.up (formsTmul F x η))) =
          (CategoryTheory.toSheafify (smallTopology S) (tensorDifferentialFormsPresheaf F 2)).app
            (op A) (ULift.up (formsTmul F x (formsWedgeOne η ω)))) ∧
      (∀ (A : CrystallineThickening S) (s : F.val.obj (op A))
          (ω : (crysDifferentialForms S 1).obj (op A)),
        (crystalExtensionCris hF).hom.app (op A)
            ((CategoryTheory.toSheafify (smallTopology S) (tensorDifferentialFormsPresheaf F 1)).app
              (op A) (ULift.up (formsTmul F s ω))) =
          crystalWedgeCrisApp F A ω ((crystalConnectionCris hF).hom.app (op A) (ULift.up s)) +
            (show (tensorDifferentialFormsSheaf F 2).obj.obj (op A) from
              (CategoryTheory.toSheafify (smallTopology S)
                (tensorDifferentialFormsPresheaf F 2)).app
                  (op A) (ULift.up (formsTmul F s (formsDeRham A ω))))) ∧
      crystalConnectionCris hF ≫ crystalExtensionCris hF = 0) :=
  ⟨crystalConnectionCris_isConnection hF, crystalConnectionCris_isIntegrable hF⟩

end Crystalline.GlobalCrystallineSituation.SmallSite

end
