module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.CechGlobalSliceAway
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.KoszulDualProZero
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Koszul tower of Tag 0A0E is pro-zero below the top degree on the slice over an affine open

`KoszulDualProZero.lean` proves the pro-vanishing of the cohomology sheaves of the tower of
[Stacks, Tag 0A0E] in two forms: at a flat Noetherian model uniform over a basis
(`Stacks.KoszulProZero.exists_koszulDualSystemOn_homologyMap_eq_zero_of_model`, on an arbitrary
ringed site and with **no** compactness hypothesis), and on a **quasi-compact** locally Noetherian
scheme (`Stacks.KoszulProZero.exists_koszulDualSystemOn_homologyMap_eq_zero_of_coherent`, where the
Artin–Rees level is a maximum over a finite affine cover).

This file discharges the model hypothesis on the **slice site over an affine open**, where one
model serves the whole site and no compactness of the ambient scheme is used:

* the site is `(Stacks.SheafOfModules.opensRingedSite Y.sheaf).over U` for an affine open `U` of a
  locally Noetherian scheme `Y`, which is a `RingedSite` and not a scheme, so `[CompactSpace]` is
  not a statable hypothesis there;
* the model is the single pair `A = Γ(Y, U)`, `M = Γ(ℱ, U)` — a Noetherian ring by
  `AlgebraicGeometry.IsLocallyNoetherian.component_noetherian` and a finite module over it by
  `AlgebraicGeometry.moduleFinite_sections_on_affine`;
* the covering families are the basic opens `Y.basicOpen g ⊆ V` for `g ∈ Γ(Y, U)`, which cover
  every object `V ⟶ U` of the slice by `AlgebraicGeometry.IsAffineOpen.exists_basicOpen_le`; over
  such a basic open the structure sections are flat over `A`
  (`Stacks.KoszulProZero.flat_sections_basicOpen`) and the sections of `ℱ` are the corresponding
  base change of `M` (`Stacks.KoszulProZero.basicOpenModelIso`).

The scheme-level discharge of `KoszulHomologyProZeroScheme.lean` instead produces one model per
member of a finite affine cover and maximises the levels over it, which is the single place
quasi-compactness enters the chain of `Completion/KoszulAdicCompletionLimit.lean`. Here the whole
basis of basic opens of `U` is served by the one model attached to `U`, so the level is uniform
for free.

## Main results

* `Stacks.KoszulProZero.exists_koszulDualSystemOn_over_homologyMap_eq_zero` — **the cohomology
  sheaves of the tower of [Stacks, Tag 0A0E] are pro-zero below the top degree on the slice over
  an affine open of a locally Noetherian scheme**, for the restriction of a coherent module, with
  no compactness hypothesis on the ambient scheme.

## References

* [Stacks Project, Tag 01P7](https://stacks.math.columbia.edu/tag/01P7)
* [Stacks Project, Tag 0A0E](https://stacks.math.columbia.edu/tag/0A0E)
* [Stacks Project, Tag 0A0K](https://stacks.math.columbia.edu/tag/0A0K)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.KoszulCoefficientProIso (rTensorFunctor)

universe u

namespace Stacks.KoszulProZero

section Slice

variable (Y : Scheme.{u}) [IsLocallyNoetherian Y] {r : ℕ}
  (f : Fin r → Presheaf.globalSections
    ((_root_.Stacks.SheafOfModules.opensRingedSite Y.sheaf).O.obj ⋙ forget CommRingCat.{u}))
  (ℱ : Y.Modules) [ℱ.IsCoherent] (U : Y.affineOpens)

/-- **The cohomology sheaves of the tower of the Koszul formula of [Stacks, Tag 0A0E] are
pro-zero away from the degree carrying the quotient, on the slice site over an affine open.**

Let `Y` be a locally Noetherian scheme — *not* assumed quasi-compact — let `f_1, …, f_r` be
global sections of `𝒪_Y`, let `ℱ` be a coherent `𝒪_Y`-module and let `U` be an affine open. On
the localization of the opens ringed site of `Y` at `U`, for the restricted family and the
restricted module, every level `n` and every degree `p` below the top degree `r` admit a later
level `m` at which the transition of 0A0E's tower induces the zero map on the degree-`p`
cohomology sheaf.

The proof is `Stacks.KoszulProZero.exists_koszulDualSystemOn_homologyMap_eq_zero_of_model` at the
single model `A = Γ(Y, U)`, `a_i = f_i|_U`, `M = Γ(ℱ, U)`: the basic opens of `U` are a basis of
the slice site, over each of them `Γ(𝒪_Y, Y.basicOpen g)` is a localization of `A` hence flat and
`Γ(ℱ, Y.basicOpen g)` is the base change of `M`, and the Artin–Rees level is computed once over
the model. No maximum over a cover is taken, which is why no quasi-compactness of `Y` appears.

The degrees `p < r` are those of the Koszul complex itself, which is concentrated in `0, …, r`;
in the shifted indexing of [Stacks, Tags 0A0E and 0A0K] they are the degrees `p - r < 0`, the
degree `0` carrying the quotient `ℱ/(f_1^{n+1}, …, f_r^{n+1})ℱ`. -/
@[sga "2 II Lemma11" "special case"]
theorem exists_koszulDualSystemOn_over_homologyMap_eq_zero (n : ℕ) (p : ℤ) (hp : p < r) :
    ∃ (m : ℕ) (hnm : n ≤ m), HomologicalComplex.homologyMap
      ((_root_.AlgebraicGeometry.RingedSite.koszulDualSystemOn
          ((_root_.Stacks.SheafOfModules.opensRingedSite Y.sheaf).over U.1)
          (fun i => _root_.AlgebraicGeometry.RingedSite.globalSectionOver
            (_root_.Stacks.SheafOfModules.opensRingedSite Y.sheaf) U.1 (f i))
          ((SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
              (_root_.Stacks.SheafOfModules.opensRingedSite Y.sheaf).O)) U.1).obj
            (show SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
              (_root_.Stacks.SheafOfModules.opensRingedSite Y.sheaf).O)) from ℱ))).map
        (homOfLE hnm).op) p = 0 := by
  obtain ⟨hqc, hft⟩ :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent ℱ
  have := hqc
  have := IsLocallyNoetherian.component_noetherian U
  have : Module.Finite Γ(Y, U.1) Γ(ℱ, U.1) :=
    AlgebraicGeometry.moduleFinite_sections_on_affine ℱ U.1 U.2
  refine exists_koszulDualSystemOn_homologyMap_eq_zero_of_model
    ((_root_.Stacks.SheafOfModules.opensRingedSite Y.sheaf).over U.1) _ _
    Γ(Y, U.1) (fun i => RingedSite.globalSectionVal (f i) (op U.1))
    (ModuleCat.of Γ(Y, U.1) Γ(ℱ, U.1)) (fun W => ?_) n p hp
  refine ⟨fun Z _ => ∃ g : Γ(Y, U.1), Z = Over.mk (homOfLE (Y.basicOpen_le g)), ?_, ?_⟩
  · intro x hx
    obtain ⟨g, hgle, hxg⟩ :=
      U.2.exists_basicOpen_le (V := W.unop.left) ⟨x, hx⟩ (leOfHom W.unop.hom hx)
    refine ⟨Y.basicOpen g, homOfLE hgle, ?_, hxg⟩
    rw [Sieve.overEquiv_iff]
    exact ⟨_, 𝟙 _, Over.homMk (homOfLE hgle), ⟨g, rfl⟩, by simp⟩
  · rintro Z i ⟨g, rfl⟩
    refine ⟨basicOpenRestrict Y U.1 g, ModuleCat.of Γ(Y, U.1) Γ(Y, Y.basicOpen g),
      fun j => ?_, flat_sections_basicOpen Y U g, ⟨basicOpenModelIso Y ℱ U g⟩⟩
    rw [RingedSite.globalSectionVal_globalSectionOver]
    exact basicOpenRestrict_globalSectionVal Y f U.1 g j

end Slice

end Stacks.KoszulProZero

end
