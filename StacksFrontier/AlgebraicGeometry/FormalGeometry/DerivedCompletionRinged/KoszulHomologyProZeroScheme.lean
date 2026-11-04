module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomFilteredColimit
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicArtinRees
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.KoszulHomologyProZero
public import StacksFrontier.AlgebraicGeometry.Properties.PrincipalOpens.Sections
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Koszul cohomology sheaves of a coherent module are pro-zero below the top degree

Let `X` be a **quasi-compact locally Noetherian** scheme, let `f_1, …, f_r` be global sections of
`𝒪_X` and let `ℱ` be a **coherent** `𝒪_X`-module. The main result of this file is that the
cohomology sheaves of the Koszul complex `koszulPowerComplexOn X f ℱ n` in every degree below the
top degree `r` are pro-zero: for every level `n` and every `p < r` there is a later level `m` at
which the downward Koszul transition induces the zero map `H^p` of sheaves.

This discharges, in exactly the setting [Stacks, Tag 0A0K] is stated in, the hypothesis that
`Stacks.KoszulProZero.exists_koszulPowerComplexOnDown_homologyMap_eq_zero` of
`KoszulHomologyProZero.lean` carries — the existence of a flat Noetherian model uniform over a
basis. The model is **not** global here: a coherent module on a locally Noetherian scheme is the
base change of a finite module over a Noetherian ring only *locally*, one model per member of a
finite affine cover. The three steps are:

* on a basic open `D(g)` of an affine open `U`, the sections of `𝒪_X` are a localization of
  `Γ(X, U)`, hence flat over it (`Stacks.KoszulProZero.flat_sections_basicOpen`), and the
  sections of `ℱ` are the corresponding base change
  (`Stacks.KoszulProZero.basicOpenModelIso`, which is [Stacks, Tag 01P7] read through
  `IsLocalizedModule.isBaseChange`). The basic opens of the members of an affine cover are a
  basis, by `AlgebraicGeometry.IsAffineOpen.exists_basicOpen_le`;
* each member `U` of the cover contributes its own Artin–Rees level, by
  `Stacks.KoszulProZero.exists_modDown_cocyclesIntoCoboundaries` applied to the Noetherian ring
  `Γ(X, U)` and the finite module `Γ(ℱ, U)`;
* **quasi-compactness enters here, and only here**: the cover is finite, so the finitely many
  levels have a maximum, and the maximum works because the property persists at later levels —
  a composite of downward Koszul transitions is a downward Koszul transition, which is
  `CategoryTheory.AlternatingCech.constDownMap_comp` and
  `Stacks.KoszulProZero.cocyclesIntoCoboundaries_modDown_of_le`.

`[CompactSpace X]` is therefore a genuine hypothesis of the theorem, not an artefact: with
infinitely many affine charts the Artin–Rees levels need not be bounded, and no single level `m`
need exist. It is an explicit hypothesis of
`Stacks.KoszulProZero.exists_koszulPowerComplexOnDown_homologyMap_eq_zero_of_coherent`, as are
`[IsLocallyNoetherian X]` and `[ℱ.IsCoherent]`; the source of [Stacks, Tag 0A0K] makes the same
three assumptions.

## Main definitions

* `Stacks.KoszulProZero.basicOpenRestrict` — the restriction ring map from the sections of `𝒪_X`
  over an open to those over a basic open of it.
* `Stacks.KoszulProZero.basicOpenModelIso` — the sections of a quasi-coherent module over a
  basic open of an affine open, as the base change of its sections over that affine open.

## Main results

* `Stacks.KoszulProZero.flat_sections_basicOpen` — the sections of `𝒪_X` over a basic open of an
  affine open are flat over the sections on that affine open.
* `Stacks.KoszulProZero.exists_koszulPowerComplexOnDown_homologyMap_eq_zero_of_coherent` —
  **the pro-vanishing of the Koszul cohomology sheaves below the top degree, for a coherent
  module on a quasi-compact locally Noetherian scheme**, with no hypothesis carried.

## References

* [Stacks Project, Tag 01P7](https://stacks.math.columbia.edu/tag/01P7)
* [Stacks Project, Tag 0913](https://stacks.math.columbia.edu/tag/0913)
* [Stacks Project, Tag 0921](https://stacks.math.columbia.edu/tag/0921)
* [Stacks Project, Tag 0A0K](https://stacks.math.columbia.edu/tag/0A0K)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.AlternatingCech
open Stacks.KoszulCoefficientProIso (rTensorFunctor)

universe u

namespace Stacks.KoszulProZero

variable (Y : Scheme.{u})

/-- The restriction ring map from the sections of `𝒪_X` over an open to those over a basic open
of it. -/
@[reducible] def basicOpenRestrict (U : Y.Opens) (g : Γ(Y, U)) :
    Γ(Y, U) →+* Γ(Y, Y.basicOpen g) :=
  (Y.presheaf.map (homOfLE (Y.basicOpen_le g)).op).hom

section Model

variable {r : ℕ}
  (f : Fin r → Presheaf.globalSections
    ((_root_.Stacks.SheafOfModules.opensRingedSite Y.sheaf).O.obj ⋙ forget CommRingCat.{u}))
  (ℱ : Y.Modules)

/-- A global section of `𝒪_X` restricts to a basic open as the restriction of its value over the
ambient open. -/
theorem basicOpenRestrict_globalSectionVal (U : Y.Opens) (g : Γ(Y, U)) (i : Fin r) :
    basicOpenRestrict Y U g (RingedSite.globalSectionVal (f i) (op U)) =
      RingedSite.globalSectionVal (f i) (op (Y.basicOpen g)) :=
  RingedSite.globalSectionVal_map (f i) (homOfLE (Y.basicOpen_le g)).op

/-- **The sections of `𝒪_X` over a basic open of an affine open are a flat algebra over the
sections on that affine open**, being a localization of them. -/
theorem flat_sections_basicOpen (U : Y.affineOpens) (g : Γ(Y, U.1)) :
    Module.Flat Γ(Y, U.1) Γ(Y, Y.basicOpen g) :=
  have : IsLocalization.Away g Γ(Y, Y.basicOpen g) := U.2.isLocalization_basicOpen g
  IsLocalization.flat _ (Submonoid.powers g)

/-- **The sections of a quasi-coherent module over a basic open of an affine open are the base
change of its sections over that affine open**, along the flat algebra of the previous result.
This is [Stacks, Tag 01P7], read through `IsLocalizedModule.isBaseChange`. -/
def basicOpenModelIso (U : Y.affineOpens) [ℱ.IsQuasicoherent] (g : Γ(Y, U.1)) :
    (Stacks.KoszulProZero.modelSectionsFunctor
        (_root_.Stacks.SheafOfModules.opensRingedSite Y.sheaf)
        (op (Y.basicOpen g)) (basicOpenRestrict Y U.1 g)).obj ℱ ≅
      (rTensorFunctor (ModuleCat.of Γ(Y, U.1) Γ(Y, Y.basicOpen g))).obj
        (ModuleCat.of Γ(Y, U.1) Γ(ℱ, U.1)) := by
  haveI : IsLocalization.Away g Γ(Y, Y.basicOpen g) := U.2.isLocalization_basicOpen g
  letI : Module Γ(Y, U.1) Γ(ℱ, Y.basicOpen g) :=
    Module.compHom Γ(ℱ, Y.basicOpen g) (basicOpenRestrict Y U.1 g)
  haveI : IsScalarTower Γ(Y, U.1) Γ(Y, Y.basicOpen g) Γ(ℱ, Y.basicOpen g) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  haveI : IsLocalizedModule.Away g
      (Scheme.Modules.restrictionLinearMap ℱ (homOfLE (Y.basicOpen_le g))) :=
    isLocalizedModule_restriction_basicOpen_of_qcqs ℱ U.2.isCompact U.2.isQuasiSeparated g
  have hbc : IsBaseChange Γ(Y, Y.basicOpen g)
      (Scheme.Modules.restrictionLinearMap ℱ (homOfLE (Y.basicOpen_le g))) :=
    IsLocalizedModule.isBaseChange (Submonoid.powers g) _ _
  exact LinearEquiv.toModuleIso
    ((hbc.equiv.restrictScalars Γ(Y, U.1)).symm.trans
      (TensorProduct.comm Γ(Y, U.1) Γ(Y, Y.basicOpen g) Γ(ℱ, U.1)))

end Model

/-! ## The discharge on a quasi-compact locally Noetherian scheme -/

section Coherent

variable [IsLocallyNoetherian Y] [CompactSpace Y] {r : ℕ}
  (f : Fin r → Presheaf.globalSections
    ((_root_.Stacks.SheafOfModules.opensRingedSite Y.sheaf).O.obj ⋙ forget CommRingCat.{u}))
  (ℱ : Y.Modules) [ℱ.IsCoherent]

/-- **The Koszul cohomology sheaves of a coherent module on a quasi-compact locally Noetherian
scheme are pro-zero below the top degree.**

For every level `n` and every degree `p` below the top degree `r` there is a later level `m` at
which the downward Koszul transition induces the zero map on the degree-`p` cohomology *sheaf*.
Nothing is assumed beyond the three hypotheses of the source: the scheme is quasi-compact and
locally Noetherian and the module is coherent. Quasi-compactness is what makes the finitely many
Artin–Rees levels of a finite affine cover have a maximum; local Noetherianness and coherence are
what give each member of the cover a Noetherian ring of functions and a finite module of
sections.

Since the Koszul complex is concentrated in the degrees `0, …, r` and its top cohomology sheaf is
`ℱ/(f_1^{n+1}, …, f_r^{n+1})ℱ`, this is the pro-vanishing of every cohomology sheaf other than
that quotient — in the homological indexing of [Stacks, Tags 0A0E and 0A0K], the pro-vanishing of
`H^{-j}` for `j > 0`. -/
@[sga "2 II Lemma11" "partial"]
theorem exists_koszulPowerComplexOnDown_homologyMap_eq_zero_of_coherent (n : ℕ) (p : ℤ)
    (hp : p < r) :
    ∃ (m : ℕ) (hnm : n ≤ m), HomologicalComplex.homologyMap
      (RingedSite.koszulPowerComplexOnDown
        (_root_.Stacks.SheafOfModules.opensRingedSite Y.sheaf) f ℱ hnm)
        p = 0 := by
  classical
  obtain ⟨hqc, hft⟩ :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent ℱ
  have hW : ∀ W : Y.affineOpens,
      IsNoetherianRing Γ(Y, W.1) ∧ Module.Finite Γ(Y, W.1) Γ(ℱ, W.1) := fun W =>
    ⟨IsLocallyNoetherian.component_noetherian W,
      AlgebraicGeometry.moduleFinite_sections_on_affine ℱ W.1 W.2⟩
  have hlev : ∀ W : Y.affineOpens, ∃ m : ℕ, ∃ hnm : n ≤ m,
      CocyclesIntoCoboundaries
        (modDown (A := Γ(Y, W.1)) (fun i => RingedSite.globalSectionVal (f i) (op W.1))
          (ModuleCat.of Γ(Y, W.1) Γ(ℱ, W.1)) hnm) p := by
    intro W
    obtain ⟨_, _⟩ := hW W
    exact exists_modDown_cocyclesIntoCoboundaries _ _ n p hp
  choose cst hcstn hcst using hlev
  have hcov : (Set.univ : Set Y) ⊆ ⋃ W : Y.affineOpens, (W.1 : Set Y) := by
    intro x _
    exact Set.mem_iUnion.2 (TopologicalSpace.Opens.mem_iSup.mp
      ((iSup_affineOpens_eq_top Y).ge (Set.mem_univ x)))
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun W : Y.affineOpens => (W.1 : Set Y)) (fun W => W.1.2) hcov
  have hcover : ∀ x : Y, ∃ W ∈ s, x ∈ W.1 := fun x => by simpa using hs (Set.mem_univ x)
  refine ⟨n ⊔ s.sup cst, le_sup_left, ?_⟩
  refine homologyMap_eq_zero_of_sections _ f ℱ _ p (fun U => ?_)
  refine ⟨fun V _ => ∃ (W : Y.affineOpens) (_ : W ∈ s) (g : Γ(Y, W.1)),
    V = Y.basicOpen g, ?_, ?_⟩
  · intro x hxU
    obtain ⟨W, hWs, hxW⟩ := hcover x
    obtain ⟨g, hgU, hxg⟩ := W.2.exists_basicOpen_le (⟨x, hxU⟩ : U.unop) hxW
    exact ⟨Y.basicOpen g, homOfLE hgU,
      ⟨Y.basicOpen g, 𝟙 _, homOfLE hgU, ⟨W, hWs, g, rfl⟩, by simp⟩, hxg⟩
  · rintro V i ⟨W, hWs, g, rfl⟩
    obtain ⟨_, _⟩ := hW W
    have : Module.Flat Γ(Y, W.1) (ModuleCat.of Γ(Y, W.1) Γ(Y, Y.basicOpen g)) :=
      flat_sections_basicOpen Y W g
    have hle : cst W ≤ n ⊔ s.sup cst := le_sup_of_le_right (Finset.le_sup hWs)
    exact sectionsCocyclesIntoCoboundaries_of_model _ f ℱ (A := Γ(Y, W.1))
      (fun i => RingedSite.globalSectionVal (f i) (op W.1))
      (ModuleCat.of Γ(Y, W.1) Γ(ℱ, W.1))
      (ModuleCat.of Γ(Y, W.1) Γ(Y, Y.basicOpen g))
      (op (Y.basicOpen g)) (basicOpenRestrict Y W.1 g)
      (fun i => basicOpenRestrict_globalSectionVal Y f W.1 g i)
      (basicOpenModelIso Y ℱ W g) _ p
      (cocyclesIntoCoboundaries_modDown_of_le _ _ hle (hcstn W) p (hcst W))

end Coherent

end Stacks.KoszulProZero

end
