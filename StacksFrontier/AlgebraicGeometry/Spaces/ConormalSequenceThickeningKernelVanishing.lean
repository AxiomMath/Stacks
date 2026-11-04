module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceDefiningIdealFibreSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceInverseImageDerivation
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ConormalModuleInverseImageKernel
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealBijection
public import StacksFrontier.AlgebraicGeometry.Spaces.LiftDifferenceDescent

/-!
# The transpose of a derivation vanishing on the defining ideal kills the kernel of `i^♯`

Let `Z ⊆ X` be a closed subspace of an algebraic space over a base `Bb`, with inclusion
`i : Z ⟶ X`, let `M` be an `𝒪_Z`-module and let `D : 𝒪_X ⟶ i_*M` be a `Bb`-derivation vanishing
on every local section of the defining ideal sheaf `𝓘`.  Its transpose along `i^{-1} ⊣ i_*`,
`AlgebraicGeometry.Space.inverseImageDerivationFun`, is a function
`(i^{-1}𝒪_X)(W) → M(W)` over every object `W` of the small étale site of `Z`, and
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceInverseImageDerivation.lean` proves it
additive, Leibniz through `i^♯ : i^{-1}𝒪_X ⟶ 𝒪_Z`, and compatible with étale restriction.

This file proves the fourth identity, **for an arbitrary closed subspace**: the transpose
kills every section of `i^{-1}𝒪_X` that `i^♯` kills.  Together with the three identities there
this completes `Stacks.Sites.QuotientDerivation` at `q := i^♯` in its inverse-image form.

## How the general case goes, and what the thickening case is

The identity is not a transport of anything `D` satisfies on sections: a section of `i^{-1}𝒪_X`
over `W` is only *locally* an inverse image of a section of `𝒪_X`, so the vanishing of `D` on
`𝓘` reaches it only once `i^{-1}` has been seen to preserve the presentation of `𝓘` as the
kernel of `i^♯ : 𝒪_X ⟶ i_*𝒪_Z`.  That presentation — `𝓘` as the fibre of `i^♯` over the zero
section of sheaves of *sets* — is
`AlgebraicGeometry.Space.isPullback_definingIdealSheaf` of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceDefiningIdealFibreSquare.lean`, and
`AlgebraicGeometry.Space.exists_inverseImage_definingIdealSheaf_eq` there carries it through
`i^{-1}` by left exactness and reads it on sections.  Its one geometric input is that the
**counit** `i^{-1}i_*𝒪_Z ⟶ 𝒪_Z` is invertible, which is [Stacks Project, Tag 04E5], part (1),
for the closed immersion `i`.  So the vanishing is the transport of
`AlgebraicGeometry.Space.submoduleInclSheafSets_comp_derivationHom`, the hypothesis `hvanish`
read as an identity of morphisms, along `i^{-1}`.

The thickening-specific identification of the conormal module with that kernel is also proved
here, and it is a different statement.  For a thickening the ideal machinery of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/InverseImageKernelIdeal.lean` applies, because the
unit `𝒪_X ⟶ i_*i^{-1}𝒪_X` is an *isomorphism* there
(`AlgebraicGeometry.Space.isIso_thickeningRingUnit`), and that is exactly the hypothesis that
machinery takes — the **unit**, where the general route needs only the **counit**.  Two of its
consequences are used:

* `AlgebraicGeometry.Space.exists_conormalInverseImageι_eq`: every section of `i^{-1}𝒪_X` killed
  by `i^♯` is the image of a section of the conormal module under
  `AlgebraicGeometry.Space.conormalInverseImageι`;
* `AlgebraicGeometry.Space.exists_structureSharp_eq_zero_map_conormalInverseImageι_val_app`: the
  direct image of that inclusion, on sections over the small étale site of `X`, is the unit
  applied to a section of `𝒪_X` killed by `i^♯ : 𝒪_X ⟶ i_*𝒪_Z` — that is, to a local section of
  the defining ideal.

From them `AlgebraicGeometry.Space.inverseImageDerivationFun_conormalInverseImageι_eq_zero` — the
transpose kills the image of the conormal module — is proved by comparing two morphisms of
sheaves of sets on the site of `Z` after applying `i_*`, which is **faithful** for a closed
immersion (`AlgebraicGeometry.Space.faithful_thickeningToposHom_pushforward`): over the site of
`X` the transpose is computed by `D` itself, and `D` vanishes there by hypothesis.

The hypothesis that `D` vanishes on `𝓘` is carried as a named argument throughout; the
thickening hypothesis is carried only by the conormal-module statements, which is where it is
used.

## Main definitions

* `AlgebraicGeometry.Space.inverseImageQuotientDerivation`: **`D` as
  `Stacks.Sites.QuotientDerivation` data through `i^♯ : i^{-1}𝒪_X ⟶ 𝒪_Z`**, all four fields, for
  an arbitrary closed subspace.

## Main results

* `AlgebraicGeometry.Space.pushforwardSections_inverseImageDerivationHom_thickeningRingUnit`:
  **the direct image of the transpose, evaluated at the unit, computes `D`.**  This is
  `AlgebraicGeometry.Space.homEquiv_inverseImageDerivationHom` read on sections, and it is where
  the transpose meets the derivation it was built from.
* `AlgebraicGeometry.Space.inverseImageDerivationFun_conormalInverseImageι_eq_zero`: the
  transpose kills the image of the conormal module, for a first-order thickening.
* `AlgebraicGeometry.Space.submoduleInclSheafSets_comp_derivationHom` and
  `AlgebraicGeometry.Space.inverseImageDerivationFun_map_submoduleInclSheafSets_eq_zero`: the
  vanishing of `D` on `𝓘` as an identity of morphisms, and its transport along `i^{-1}`.
* `AlgebraicGeometry.Space.inverseImageDerivationFun_eq_zero_of_app_eq_zero`: **the fourth
  identity** — the transpose kills every section of `i^{-1}𝒪_X` that `i^♯` kills.  For an
  arbitrary closed subspace.

## References

* [Stacks Project, Tag 05ZA](https://stacks.math.columbia.edu/tag/05ZA), the conormal sequence.
* [Stacks Project, Tag 08M3](https://stacks.math.columbia.edu/tag/08M3), the kernel ideal of a
  closed immersion of topoi, which is the machinery the thickening hypothesis feeds.
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB), the defining ideal sheaf
  as the kernel of the structure map.
* [Stacks Project, Tag 04E5](https://stacks.math.columbia.edu/tag/04E5), part (1), the full
  faithfulness of the direct image along a closed immersion, equivalently the invertibility of
  the counit, which is what the general route spends.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open Stacks.Sites Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Bb : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1) (b : X ⟶ Bb)
  (M : Modules.{u, u} B S hS Z.1.toFunctor Z.2.1)
  (D : ((modulePushforward B S hS (subspaceInclusion B S hS X Z)).obj M).val.Derivation'
    (structureSharpInverseImage B S hS b).hom)

/-- **The direct image of the transpose of `D`, evaluated at the unit `𝒪_X ⟶ i_*i^{-1}𝒪_X`,
computes `D`.**

`AlgebraicGeometry.Space.homEquiv_inverseImageDerivationHom` says that the image of the
transpose under the hom-set bijection of `i^{-1} ⊣ i_*` is the morphism of sheaves of sets
belonging to `D`; that bijection is "precompose the direct image with the unit"
(`CategoryTheory.Adjunction.homEquiv_unit`), and the unit of sheaves of rings is the unit of
sheaves of sets on the nose, so reading the equation on sections over an object of the small
étale site of `X` gives this. -/
theorem pushforwardSections_inverseImageDerivationHom_thickeningRingUnit
    (U : (SmallEtale B S hS X.1)ᵒᵖ) (r : (structureRingSheaf B S hS X).obj.obj U) :
    ((thickeningToposHom B S hS Z).pushforward ⋙
        sectionsFunctor (SmallEtale.topology B S hS X.1) U).map
        (inverseImageDerivationHom B S hS b (subspaceInclusion B S hS X Z) M D)
        (((thickeningRingUnit B S hS Z).hom.app U) r) =
      D.d r := by
  have h : (smallEtaleRingedToposHom B S hS
          (subspaceInclusion B S hS X Z)).toToposHom.adj.unit.app
        (Sheaf.ringSheaf.{u, u, u + 1} (structureRingSheaf B S hS X)) ≫
      (smallEtaleRingedToposHom B S hS
          (subspaceInclusion B S hS X Z)).toToposHom.pushforward.map
        (inverseImageDerivationHom B S hS b (subspaceInclusion B S hS X Z) M D) =
      derivationHom B S hS b
        ((modulePushforward B S hS (subspaceInclusion B S hS X Z)).obj M) D :=
    (Adjunction.homEquiv_unit
      (adj := (smallEtaleRingedToposHom B S hS
        (subspaceInclusion B S hS X Z)).toToposHom.adj)
      (X := Sheaf.ringSheaf.{u, u, u + 1} (structureRingSheaf B S hS X))
      (Y := Sheaf.moduleSheaf.{u, u, u + 1}
        (structureRingSheaf B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)) M)
      (f := inverseImageDerivationHom B S hS b
        (subspaceInclusion B S hS X Z) M D)).symm.trans
      (homEquiv_inverseImageDerivationHom B S hS b (subspaceInclusion B S hS X Z) M D)
  have h2 : (sectionsFunctor (SmallEtale.topology B S hS X.1) U).map
      (derivationHom B S hS b
        ((modulePushforward B S hS (subspaceInclusion B S hS X Z)).obj M) D) r = D.d r :=
    sectionsFunctor_map_unaryOpHom (A := Sheaf.ringSheaf.{u, u, u + 1}
        (structureRingSheaf B S hS X))
      (E := Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS X)
        ((modulePushforward B S hS (subspaceInclusion B S hS X Z)).obj M))
      (fun _ a ↦ D.d a) (fun g a ↦ (D.d_map g a).symm) U r
  refine Eq.trans ?_ (Eq.trans
    (congrArg (fun m ↦ (sectionsFunctor (SmallEtale.topology B S hS X.1) U).map m r) h) h2)
  exact ((sectionsFunctor (SmallEtale.topology B S hS X.1) U).map_comp_apply
    ((smallEtaleRingedToposHom B S hS (subspaceInclusion B S hS X Z)).toToposHom.adj.unit.app
      (Sheaf.ringSheaf.{u, u, u + 1} (structureRingSheaf B S hS X)))
    ((smallEtaleRingedToposHom B S hS
        (subspaceInclusion B S hS X Z)).toToposHom.pushforward.map
      (inverseImageDerivationHom B S hS b (subspaceInclusion B S hS X Z) M D)) r).symm

section Vanishing

variable (hZ : IsFirstOrderThickening B S hS X Z.1)
  (hvanish : ∀ (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (x : (definingIdealSheaf B S hS X Z).toSheafOfModules.val.obj U), D.d x.1 = 0)

/-- The inclusion of the conormal module into `i^{-1}𝒪_X`, followed by the transpose of `D`, as a
morphism of the underlying sheaves of sets on the small étale site of `Z`. -/
noncomputable abbrev conormalInverseImageDerivationHom :
    Sheaf.moduleSheaf.{u, u, u + 1}
        (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z))
        ((SheafOfModules.restrictScalars
          (structureSharpRingInverseImage B S hS
            (subspaceInclusion B S hS X Z))).obj (conormalModule B S hS X Z)) ⟶
      Sheaf.moduleSheaf.{u, u, u + 1}
        (structureRingSheaf B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)) M :=
  (Sheaf.moduleSheafFunctor
      (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z))).map
      (conormalInverseImageι B S hS Z hZ) ≫
    inverseImageDerivationHom B S hS b (subspaceInclusion B S hS X Z) M D

/-- The zero morphism of `i^{-1}𝒪_X`-modules from the conormal module to `M`, read on the
underlying sheaves of sets.  This is what
`AlgebraicGeometry.Space.conormalInverseImageDerivationHom` is compared with. -/
noncomputable abbrev conormalInverseImageZeroHom :
    Sheaf.moduleSheaf.{u, u, u + 1}
        (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z))
        ((SheafOfModules.restrictScalars
          (structureSharpRingInverseImage B S hS
            (subspaceInclusion B S hS X Z))).obj (conormalModule B S hS X Z)) ⟶
      Sheaf.moduleSheaf.{u, u, u + 1}
        (structureRingSheaf B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)) M :=
  (Sheaf.moduleSheafFunctor
      (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z))).map
    (0 : (SheafOfModules.restrictScalars
          (structureSharpRingInverseImage B S hS
            (subspaceInclusion B S hS X Z))).obj (conormalModule B S hS X Z) ⟶
      (SheafOfModules.restrictScalars
          (structureSharpRingInverseImage B S hS
            (subspaceInclusion B S hS X Z))).obj M)

include hZ hvanish

/-- **The two morphisms have the same direct image.**  Over an object of the small étale site of
`X` the direct image of the first is the transport of the inclusion followed by the direct image
of the transpose; the transport of the inclusion lands in the unit of a local section of the
defining ideal, and the direct image of the transpose evaluated there is `D` of that section,
which vanishes. -/
theorem pushforward_conormalInverseImageDerivationHom_eq :
    (thickeningToposHom B S hS Z).pushforward.map
        (conormalInverseImageDerivationHom B S hS Z b M D hZ) =
      (thickeningToposHom B S hS Z).pushforward.map
        (conormalInverseImageZeroHom B S hS Z M) := by
  refine hom_ext_sections fun U t ↦ ?_
  obtain ⟨r, hr0, hrq⟩ :=
    exists_structureSharp_eq_zero_map_conormalInverseImageι_val_app B S hS Z hZ U t
  have hzero : ((thickeningToposHom B S hS Z).pushforward ⋙
      sectionsFunctor (SmallEtale.topology B S hS X.1) U).map
      (conormalInverseImageZeroHom B S hS Z M) t =
        (0 : ((modulePushforward B S hS
          (subspaceInclusion B S hS X Z)).obj M).val.obj U) := by
    have : (thickeningTransport B S hS Z).Additive :=
      Stacks.SheafOfModules.IdealTransport.additive_transport
        (SmallEtale.topology B S hS X.1) (thickeningToposHom B S hS Z).pushforward
        (thickeningRingUnit B S hS Z)
    change (((thickeningTransport B S hS Z).map 0).val.app U) t = 0
    erw [Functor.map_zero]
    rfl
  refine Eq.trans (((thickeningToposHom B S hS Z).pushforward ⋙
      sectionsFunctor (SmallEtale.topology B S hS X.1) U).map_comp_apply _ _ t)
    (Eq.trans ?_ hzero.symm)
  refine Eq.trans (congrArg (((thickeningToposHom B S hS Z).pushforward ⋙
      sectionsFunctor (SmallEtale.topology B S hS X.1) U).map
        (inverseImageDerivationHom B S hS b (subspaceInclusion B S hS X Z) M D)) hrq) ?_
  refine Eq.trans
    (pushforwardSections_inverseImageDerivationHom_thickeningRingUnit B S hS Z b M D U r) ?_
  exact hvanish U ⟨r, (mem_definingIdealAt_iff B S hS X Z U r).2 hr0⟩

/-- **The transpose of `D` kills the image of the conormal module.**  The direct image of sheaves
of sets along the inclusion of a closed subspace is faithful, by Stacks 04E5, part (1), so this
is `AlgebraicGeometry.Space.pushforward_conormalInverseImageDerivationHom_eq` read back on the
small étale site of `Z`. -/
theorem inverseImageDerivationFun_conormalInverseImageι_eq_zero
    (W : (SmallEtale B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
    (m : ((SheafOfModules.restrictScalars
        (structureSharpRingInverseImage B S hS
          (subspaceInclusion B S hS X Z))).obj (conormalModule B S hS X Z)).val.obj W) :
    inverseImageDerivationFun B S hS b (subspaceInclusion B S hS X Z) M D W
        ((conormalInverseImageι B S hS Z hZ).val.app W m) = 0 := by
  have h := (thickeningToposHom B S hS Z).pushforward.map_injective
    (pushforward_conormalInverseImageDerivationHom_eq B S hS Z b M D hZ hvanish)
  exact congrArg
    (fun g ↦ (sectionsFunctor (SmallEtale.topology B S hS
      (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1) W).map g m) h

end Vanishing

/-! ### The vanishing on the kernel of the structure map, for an arbitrary closed subspace -/

section GeneralVanishing

variable (hvanish : ∀ (U : (SmallEtale B S hS X.1)ᵒᵖ)
  (x : (definingIdealSheaf B S hS X Z).toSheafOfModules.val.obj U), D.d x.1 = 0)

include hvanish

/-- **The inclusion of the defining ideal sheaf followed by `D` is the zero morphism** of
sheaves of sets on the small étale site of `X`.

This is the hypothesis `hvanish` read as an identity of morphisms rather than of values, which
is the shape that transports along `i^{-1}`: the inverse image of a morphism out of the terminal
sheaf is computed because `i^{-1}` preserves finite products. -/
theorem submoduleInclSheafSets_comp_derivationHom :
    submoduleInclSheafSets (definingIdealSheaf B S hS X Z) ≫
        derivationHom B S hS b
          ((modulePushforward B S hS (subspaceInclusion B S hS X Z)).obj M) D =
      zeroModuleHom
        (Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS X)
          (definingIdealSheaf B S hS X Z).toSheafOfModules)
        (structureRingSheaf B S hS X)
        ((modulePushforward B S hS (subspaceInclusion B S hS X Z)).obj M) := by
  refine hom_ext_sections fun U x ↦ ?_
  refine Eq.trans ((sectionsFunctor (SmallEtale.topology B S hS X.1) U).map_comp_apply _ _ x) ?_
  refine Eq.trans (hvanish U x) ?_
  exact (map_zeroModuleHom _ (structureRingSheaf B S hS X)
    ((modulePushforward B S hS (subspaceInclusion B S hS X Z)).obj M)
    (sectionsFunctor (SmallEtale.topology B S hS X.1) U) x).symm

/-- **The transpose of `D` kills the image of `i^{-1}𝓘`.**

This is the transport of
`AlgebraicGeometry.Space.submoduleInclSheafSets_comp_derivationHom` along `i^{-1}`, by exactly
the three steps
`AlgebraicGeometry.Space.inverseImageDerivationFun_map_structureSharpInverseImageSet_eq_zero`
takes for the vanishing on the base: the transpose is the inverse image of the derivation
followed by the counit, the inverse image of a morphism out of a terminal object is the
transported zero section (`Stacks.Sheaves.ToposPullback.map_zeroModuleHom`), and the counit
sends that to zero
(`AlgebraicGeometry.Space.inverseImageCounitFun_moduleZeroObj`).  No thickening hypothesis and
no closed immersion enter here; they enter in
`AlgebraicGeometry.Space.exists_inverseImage_definingIdealSheaf_eq`. -/
theorem inverseImageDerivationFun_map_submoduleInclSheafSets_eq_zero
    (W : (SmallEtale B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
    (m : (inverseImageSections B S hS (subspaceInclusion B S hS X Z) W).obj
      (Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS X)
        (definingIdealSheaf B S hS X Z).toSheafOfModules)) :
    inverseImageDerivationFun B S hS b (subspaceInclusion B S hS X Z) M D W
        ((inverseImageSections B S hS (subspaceInclusion B S hS X Z) W).map
          (submoduleInclSheafSets (definingIdealSheaf B S hS X Z)) m) = 0 := by
  refine Eq.trans (inverseImageDerivationFun_eq B S hS b
    (subspaceInclusion B S hS X Z) M D W _) ?_
  refine Eq.trans (congrArg
    (inverseImageCounitFun B S hS (subspaceInclusion B S hS X Z) M W)
    ((inverseImageSections B S hS (subspaceInclusion B S hS X Z) W).map_comp_apply _ _ m).symm) ?_
  refine Eq.trans (congrArg
    (fun n ↦ inverseImageCounitFun B S hS (subspaceInclusion B S hS X Z) M W
      ((inverseImageSections B S hS (subspaceInclusion B S hS X Z) W).map n m))
    (submoduleInclSheafSets_comp_derivationHom B S hS Z b M D hvanish)) ?_
  refine Eq.trans (congrArg
    (inverseImageCounitFun B S hS (subspaceInclusion B S hS X Z) M W)
    (map_zeroModuleHom _ (structureRingSheaf B S hS X)
      ((modulePushforward B S hS (subspaceInclusion B S hS X Z)).obj M)
      (inverseImageSections B S hS (subspaceInclusion B S hS X Z) W) m)) ?_
  exact inverseImageCounitFun_moduleZeroObj B S hS (subspaceInclusion B S hS X Z) M W

/-- **The fourth identity: the transpose of `D` kills every section of `i^{-1}𝒪_X` that
`i^♯ : i^{-1}𝒪_X ⟶ 𝒪_Z` kills.**  This is the `d_eq_zero_of_app_eq_zero` field of
`Stacks.Sites.QuotientDerivation` at `q := i^♯` in its inverse-image form, and it holds for an
**arbitrary closed subspace**: no thickening hypothesis.

Every such section is the image of a section of `i^{-1}𝓘`, by
`AlgebraicGeometry.Space.exists_inverseImage_definingIdealSheaf_eq` — the fibre-square
presentation of the defining ideal sheaf carried through the left exact `i^{-1}`, with the
counit of the closed immersion identifying the two kernels — and the transpose kills those by
`AlgebraicGeometry.Space.inverseImageDerivationFun_map_submoduleInclSheafSets_eq_zero`. -/
theorem inverseImageDerivationFun_eq_zero_of_app_eq_zero
    (W : (SmallEtale B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
    (a : (structureRingSheafInverseImage B S hS
      (subspaceInclusion B S hS X Z)).obj.obj W)
    (ha : ((structureSharpRingInverseImage B S hS
      (subspaceInclusion B S hS X Z)).hom.app W) a = 0) :
    inverseImageDerivationFun B S hS b (subspaceInclusion B S hS X Z) M D W a = 0 := by
  obtain ⟨m, hm⟩ := exists_inverseImage_definingIdealSheaf_eq B S hS Z W a ha
  exact (congrArg (inverseImageDerivationFun B S hS b
      (subspaceInclusion B S hS X Z) M D W) hm).symm.trans
    (inverseImageDerivationFun_map_submoduleInclSheafSets_eq_zero
      B S hS Z b M D hvanish W m)

/-- **The derivation data of `D` on the small étale site of `Z`**, through the inverse-image form
`i^♯ : i^{-1}𝒪_X ⟶ 𝒪_Z` of the structure map.

The four fields are identities about the transpose
`AlgebraicGeometry.Space.inverseImageDerivationFun`: additivity and the Leibniz rule through
`i^♯` from `StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceInverseImageDerivation.lean`,
compatibility with étale restriction from the naturality of the transpose there, and the
vanishing on the sections `i^♯` kills from
`AlgebraicGeometry.Space.inverseImageDerivationFun_eq_zero_of_app_eq_zero` above.

This is the shape `AlgebraicGeometry.Space.descendedDerivation` consumes: `i^♯` in its
inverse-image form is locally surjective at the inclusion of a closed subspace, by the instance
`AlgebraicGeometry.Space.isLocallySurjective_structureSharpRingInverseImage_subspaceInclusion`,
so this descends to a derivation of `𝒪_Z` once the vanishing on the sections read from the base
is supplied. -/
noncomputable def inverseImageQuotientDerivation :
    QuotientDerivation
      (structureSharpRingInverseImage B S hS (subspaceInclusion B S hS X Z)) M where
  d {W} := AddMonoidHom.mk'
    (inverseImageDerivationFun B S hS b (subspaceInclusion B S hS X Z) M D W)
    (inverseImageDerivationFun_add B S hS b (subspaceInclusion B S hS X Z) M D W)
  d_mul := inverseImageDerivationFun_mul B S hS b (subspaceInclusion B S hS X Z) M D _
  d_map f x := inverseImageDerivationFun_map B S hS b (subspaceInclusion B S hS X Z) M D f x
  d_eq_zero_of_app_eq_zero a ha :=
    inverseImageDerivationFun_eq_zero_of_app_eq_zero B S hS Z b M D hvanish _ a ha

end GeneralVanishing

end AlgebraicGeometry.Space

end
