module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.BaseChangeAbelianDegreewise
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.DirectImageConcentration
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.RestrictedSiteSections

/-!
# Local-to-global vanishing of crystalline cohomology through the Zariski topos

Fix a global crystalline situation `(p, (S, I, γ), X)` of [Stacks, Tag 07MF] and an abelian
sheaf `F` on `Cris(X/S)`. Suppose that for every affine open `V` of `X` mapping into an affine
open `W` of `S` the cohomology `H^j(Cris(V/S|_W), F|)` of the restricted situation vanishes in
every degree `j > d`. If `X` is quasi-compact and quasi-separated of Krull dimension at most `δ`,
then `H^j(Cris(X/S), F) = 0` for every `j > d + δ`.

The proof runs through `u_{X/S} : Cris(X/S) → X_Zar`:

* `R^j u_{X/S, *}F` is the sheafification of the presheaf `V ↦ R^j Γ(V, u_{X/S, *} -)(F)`
  ([Stacks, Tag 072W] read as a vanishing criterion,
  `...SmallSite.isZero_rightDerived_zariskiDirectImage_of_locallyIsZero`), the affine opens over
  affine opens of `S` cover `X`, and over such an open the sections functor is the cohomology of
  the restricted site ([Stacks, Tag 07KL],
  `...SmallSite.isZero_rightDerived_zariskiDirectImageSections_of_isZero`). Hence
  `R^j u_{X/S, *}F = 0` for `j > d`, that is `Ru_{X/S, *}F ∈ D^{[0, d]}(X_Zar)`;
* `RΓ(Cris(X/S), F) = RΓ(X_Zar, Ru_{X/S, *}F)` ([Stacks, Tag 015M]) and Grothendieck's vanishing
  on the spectral space `X` of dimension `≤ δ` ([Stacks, Tag 0A3G]) through the dévissage of
  `...SmallSite.isLE_derivedZariskiGlobalSections_obj` give the bound `d + δ`.

## Main results

All in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `isZero_rightDerived_zariskiDirectImage_of_locally_vanishing`: `R^p u_{X/S, *}F = 0` for
  `p > d`.
* `isZero_higherZariskiDirectImage_of_locally_vanishing`: the same for the `ℤ`-indexed
  `higherZariskiDirectImage`.
* `subsingleton_cohomology_of_locally_vanishing`: **the abelian form**,
  `H^j(Cris(X/S), F) = 0` for `j > d + δ`.
* `isZero_cohomologyFunctor_obj_of_locally_vanishing`: the same for `cohomologyFunctor S j`.
* `isZero_homology_moduleULiftDerivedGlobalSections_of_locally_vanishing`: **the module form**,
  for a sheaf of `𝒪_{X/S}`-modules: the cohomology of `RΓ(Cris(X/S), F) ∈ D⁺(Mod_A)` vanishes in
  degrees `> d + δ`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe w w' w'' u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable (S : GlobalCrystallineSituation.{u})

/-- The local hypothesis: over every affine open `V` of `X` mapping into an affine open `W` of
`S`, the cohomology of the restricted situation `(p, S|_W, V)` with coefficients in the restriction
of `F` vanishes in every degree `> d`. -/
def LocallyVanishingAbove (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) (d : ℕ) : Prop :=
  ∀ (W : S.S.scheme.Opens) (V : S.X.Opens) (hVW : V ≤ sourceToBase S ⁻¹ᵁ W),
    IsAffineOpen V → IsAffineOpen W → ∀ p : ℕ, d < p →
      Subsingleton (cohomology (restrict S W V hVW)
        ((smallExtendAbelianRestriction S W V hVW).obj F) p)

/-- **`R^p u_{X/S, *}F = 0` for `p > d`** when the cohomology of `F` over the affine opens of `X`
lying over affine opens of `S` vanishes above `d`: `R^p u_{X/S, *}F` is the sheafification of the
presheaf of the `R^p Γ(V, u_{X/S, *} -)(F)`, which vanish on the covering family of such opens,
being the cohomology of the restricted sites. -/
theorem isZero_rightDerived_zariskiDirectImage_of_locally_vanishing
    (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) (d : ℕ)
    (hloc : LocallyVanishingAbove S F d) (p : ℕ) (hp : d < p) :
    IsZero (((zariskiDirectImage S).rightDerived p).obj F) := by
  refine isZero_rightDerived_zariskiDirectImage_of_locallyIsZero S p F fun V => ?_
  let := hasDerivedCategorySheaf S
  let := hasDerivedCategoryZariskiSheaf S
  obtain ⟨R, hR, hRaff⟩ := isCoveringFamily_isAffineOverAffine S V
  refine ⟨R, hR, fun V' f hf => ?_⟩
  obtain ⟨hV'aff, W, hWaff, hV'W⟩ := hRaff hf
  exact isZero_rightDerived_zariskiDirectImageSections_of_isZero S W V' hV'W p F
    ((subsingleton_cohomology_iff_isZero_rightDerivedGlobalSections _ _ p).1
      (hloc W V' hV'W hV'aff hWaff p hp))

section Derived

variable [HasDerivedCategory.{w} (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})]

/-- The `ℤ`-indexed form: `R^j u_{X/S, *}F = 0` for every `j > d` under the local hypothesis. -/
theorem isZero_higherZariskiDirectImage_of_locally_vanishing
    (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) (d : ℕ)
    (hloc : LocallyVanishingAbove S F d) (j : ℤ) (hj : (d : ℤ) < j) :
    IsZero ((higherZariskiDirectImage S j).obj F) := by
  obtain ⟨p, rfl⟩ : ∃ p : ℕ, j = (p : ℤ) := ⟨j.toNat, by omega⟩
  exact (Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff (zariskiDirectImage S) rfl F).2
    (isZero_rightDerived_zariskiDirectImage_of_locally_vanishing S F d hloc p (by omega))

end Derived

/-- **Local-to-global vanishing of crystalline cohomology, abelian form.** Let `X` be
quasi-compact and quasi-separated of topological Krull dimension at most `δ`, and let `F` be an
abelian sheaf on `Cris(X/S)` whose cohomology over every affine open `V` of `X` mapping into an
affine open `W` of `S`, computed on `Cris(V/S|_W)`, vanishes in degrees `> d`. Then
`H^i(Cris(X/S), F) = 0` for every `i > d + δ`. -/
theorem subsingleton_cohomology_of_locally_vanishing [CompactSpace ↥S.X]
    [QuasiSeparatedSpace ↥S.X] (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) (d δ : ℕ)
    (hdim : topologicalKrullDim ↥S.X ≤ (δ : WithBot ℕ∞)) (hloc : LocallyVanishingAbove S F d)
    (i : ℕ) (hi : d + δ < i) : Subsingleton (cohomology S F i) := by
  let := hasDerivedCategorySheaf S
  let := hasDerivedCategoryZariskiSheaf S
  let := hasDerivedCategoryAddCommGrpCat.{u}
  have hLE := isLE_derivedZariskiGlobalSections_obj S ((derivedZariskiDirectImage S).obj F) δ d
    hdim (isGE_derivedZariskiDirectImage_obj S F)
    (isLE_derivedZariskiDirectImage_obj S F (d : ℤ)
      (isZero_higherZariskiDirectImage_of_locally_vanishing S F d hloc))
  have hstep : IsZero ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} (i : ℤ)).obj
      ((derivedZariskiGlobalSectionsFunctor S).obj ((derivedZariskiDirectImage S).obj F))) :=
    (DerivedCategory.Plus.isLE_iff _ ((d : ℤ) + (δ : ℤ))).1 hLE (i : ℤ) (by omega)
  have hRΓ : IsZero ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} (i : ℤ)).obj
      ((derivedGlobalSections S).obj F)) :=
    ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} (i : ℤ)).mapIso
      ((derivedGlobalSectionsIsoDerivedZariskiDirectImageObj S).app F)).isZero_iff.2 hstep
  exact (subsingleton_cohomology_iff_isZero_rightDerivedGlobalSections S F i).2
    (((rightDerivedGlobalSectionsIso S i).app F).isZero_iff.2
      (((homologyDerivedGlobalSectionsIso S i).app F).isZero_iff.1 hRΓ))

/-- The abelian form read on `cohomologyFunctor S i`: `H^i(Cris(X/S), F)` is a zero object for
`i > d + δ`. -/
theorem isZero_cohomologyFunctor_obj_of_locally_vanishing [CompactSpace ↥S.X]
    [QuasiSeparatedSpace ↥S.X] (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) (d δ : ℕ)
    (hdim : topologicalKrullDim ↥S.X ≤ (δ : WithBot ℕ∞)) (hloc : LocallyVanishingAbove S F d)
    (i : ℕ) (hi : d + δ < i) : IsZero ((cohomologyFunctor S i).obj F) :=
  have := subsingleton_cohomology_of_locally_vanishing S F d δ hdim hloc i hi
  AddCommGrpCat.isZero_iff_subsingleton.2 this

/-- **Local-to-global vanishing of crystalline cohomology, module form.** For a sheaf `F` of
`𝒪_{X/S}`-modules whose underlying abelian sheaf satisfies the local hypothesis in degrees `> d`,
on an `X` quasi-compact and quasi-separated of topological Krull dimension at most `δ`, the
cohomology of `RΓ(Cris(X/S), F) ∈ D⁺(Mod_A)` vanishes in every degree `> d + δ`. -/
theorem isZero_homology_moduleULiftDerivedGlobalSections_of_locally_vanishing
    [HasDerivedCategory.{w} (ModuleSheaf S)]
    [HasDerivedCategory.{w'} (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))]
    [CompactSpace ↥S.X] [QuasiSeparatedSpace ↥S.X]
    (F : SheafOfModules.{u} (structureSheaf S)) (d δ : ℕ)
    (hdim : topologicalKrullDim ↥S.X ≤ (δ : WithBot ℕ∞))
    (hloc : LocallyVanishingAbove S (abelianSheaf F) d) (j : ℤ) (hj : (d : ℤ) + δ < j) :
    IsZero ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) j).obj
      (moduleULiftDerivedGlobalSections S F)) := by
  obtain ⟨i, rfl⟩ : ∃ i : ℕ, j = (i : ℤ) := ⟨j.toNat, by omega⟩
  have hab := isZero_cohomologyFunctor_obj_of_locally_vanishing S (abelianSheaf F) d δ hdim hloc i
    (by omega)
  have hforget : IsZero ((forgetBaseAction S).obj (moduleULiftCohomology S F i)) :=
    hab.of_iso (moduleULiftCohomologyIsoAbelian S F i)
  refine IsZero.of_iso ?_ (homologyModuleULiftDerivedGlobalSectionsIso S F i)
  exact ModuleCat.isZero_iff_subsingleton.2 (AddCommGrpCat.isZero_iff_subsingleton.1 hforget)

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
