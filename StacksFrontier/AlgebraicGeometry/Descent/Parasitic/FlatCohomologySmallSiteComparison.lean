module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.OverAssociatedModuleIso
public import StacksFrontier.AlgebraicGeometry.Descent.Parasitic.FlatCohomologyIdentityChart
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentSiteCohomologyComparison
public import StacksCore.Tactic.StacksAttribute

/-!
# The conclusion of [Stacks, Tag 0756] at the base, at `τ = Zariski`

Let `B` be a big fppf site, `S` a scheme below its cutoff and `𝒢` a sheaf of `𝒪`-modules on
`(Sch/S)_fppf` satisfying the two hypotheses of [Stacks, Tag 0756] at `τ = Zar`:

1. `𝒢|_{S_Zar}` is quasi-coherent;
2. for every flat, locally finitely presented `g : U → S` the canonical map
   `g^*_{Zar, small}(𝒢|_{S_Zar}) → 𝒢|_{U_Zar}` is an isomorphism.

This file proves the tag's **conclusion** `H^p(U, 𝒢) = H^p(U, 𝒢|_{U_Zar})` in the instance
`U = S`:

```
H^p((Sch/S)_fppf, 𝒢)  ≅  H^p(S, 𝒢|_{S_Zar})      for every p.
```

Both sides are `CategoryTheory.Sheaf.H`, the cohomology of a site: on the left the localized big
fppf site of `S`, on the right the small Zariski site of `S` in its presentation as the site of
opens of `S`, which is where `AlgebraicGeometry.BigFppfOver.restrictModule` lands.  The
right-hand side read on the site `AlgebraicGeometry.SmallZariski` of [Stacks, Tag 020T] (2) is
`AlgebraicGeometry.BigFppfOver.smallZariskiSiteCohomologyAddEquiv` below.

Before this file **no declaration in the development asserted the conclusion of 0756**: the four
declarations the tag was registered on all stated the one comparison step
`H^p(U, ℱ) → H^p(U, 𝒢)` resting on [Stacks, Tag 0755], with big-fppf cohomology on *both* sides.
Each is a component of the proof rather than the tag's clause, so none carries `@[stacks 0756]`
any longer.  This file adds the other half, the identification of `H^p(U, ℱ)` with small-site
cohomology by [Stacks, Tag 03DW], at `τ = Zariski` and `U = S`.

## The argument, and why it needs no localization comparison

The source's proof is: let `ℱ = (𝒢|_{S_Zar})^a` with `φ : ℱ ⟶ 𝒢` the canonical comparison map;
hypotheses (1) and (2) make `φ|_{U_Zar}` an isomorphism for every flat locally finitely presented
`U`; by [Stacks, Tag 0755] `H^p(U, ℱ) → H^p(U, 𝒢)` is then an isomorphism; and the conclusion
holds for `ℱ` by [Stacks, Tag 03P2].  Each of those three steps is already in the library:

* `ℱ` and `φ` are `AlgebraicGeometry.BigFppfOver.zariskiComparisonModule` and
  `AlgebraicGeometry.BigFppfOver.zariskiComparisonMap`, the counit of
  `AlgebraicGeometry.BigFppfOver.associatedModuleAdjunction`;
* the 0755 step with its hypothesis read on the small Zariski sites is
  `AlgebraicGeometry.bigFppfCohomology_map_bijective_of_isIso_zariskiRestriction`;
* [Stacks, Tag 03DW] clause (1) in every degree is
  `AlgebraicGeometry.bigOverQuasiCoherentSiteCohomologyAddEquiv`.

The module documentation of
`StacksFrontier/AlgebraicGeometry/Descent/Parasitic/FlatCohomologyComparison.lean`,
`StacksFrontier/AlgebraicGeometry/Descent/Parasitic/FlatCohomologyCounit.lean` and
`StacksFrontier/AlgebraicGeometry/Descent/Parasitic/FlatCohomologySectionwiseIso.lean` all record
that the right-hand side `H^p(U, 𝒢|_{U_Zar})` "is cohomology on the small site of an *object* `U`
of the big site, so it needs the localization comparison" of [Stacks, Tag 075F]
(`Stacks.Cohomology.OverObjectCohomology.h'AddEquivHOver`,
`AlgebraicGeometry.Stack.cohomologyOverObjectIso`), which is not instantiated at a big fppf site.
**At `U = S` that is not needed**, and the reason is the reading of "cohomology over `U`" the
project itself adopted: the statement of record for Stacks 0756 says "Cohomology over `T` is global
cohomology of the restriction to the big fppf site of `T`", so at `T = S` the left-hand side is
global cohomology of `(Sch/S)_fppf` itself.  The 0755 step is then applied at
`AlgebraicGeometry.BigFppfOver.opensObj B S hS ⊤`, which is a terminal object of the site by
`AlgebraicGeometry.BigFppfOver.isTerminalOpensObjTop` and is flat and locally of finite
presentation over `S` because its structure morphism is the inclusion of the open `⊤`; over a
terminal object `CategoryTheory.Sheaf.H'` and `CategoryTheory.Sheaf.H` agree by
`Stacks.Cohomology.TerminalCohomology.h'AddEquivH`.  No cohomology over a non-terminal object
occurs on either side, so no localization comparison enters.

## The `𝓕^a` bridge, which was already in the tree

The two halves meet at `ℱ`, and the library spells `ℱ` twice: 03DW is stated for
`AlgebraicGeometry.bigOverAssociatedSheaf`, the abelian sheaf of [Stacks, Tag 03DS] restricted to
a localized big `τ`-site, while the comparison pair is built from
`AlgebraicGeometry.BigFppfOver.associatedModule`, the pullback along the morphism of ringed sites.
In degree `0` the two are identified by
`AlgebraicGeometry.BigFppfOver.hZeroBaseAssociatedModuleAddEquiv`; in positive degrees no
identification was on record.

It turns out to need no new mathematics.  At `τ = fppf`
`AlgebraicGeometry.BigFppfOver.overAssociatedModule_fppf` already says that the sections-defined
`𝓕^a` of [Stacks, Tag 03DU] (3) is the pullback-sections sheaf of modules **on the nose**, and
`AlgebraicGeometry.BigFppfOver.associatedModuleIsoOverAssociatedModule` — [Stacks, Remark 03FH]
(1) at `τ = fppf`, from [Stacks, Tag 070S] (1) and [Stacks, Tag 03DT] — identifies it with the
pullback.  Applying `CategoryTheory.SheafOfModules.toSheaf` to that isomorphism lands on
`AlgebraicGeometry.bigOverAssociatedSheaf` by `rfl`:
`AlgebraicGeometry.overTopology .fppf B S hS` is `AlgebraicGeometry.BigFppfOver.topology B S hS`
by `rfl`, `AlgebraicGeometry.overToSlice .fppf B S hS` is
`CategoryTheory.Over.post B.inclusion` by `rfl`, and the sheaf conditions are propositions.  That
is `AlgebraicGeometry.BigFppfOver.bigOverAssociatedSheafIso` below, and it is the whole of the
bridge.

## Main definitions

* `Stacks.Cohomology.hAddEquivOfIso`: isomorphic abelian sheaves have the same cohomology.
* `AlgebraicGeometry.BigFppfOver.bigOverAssociatedSheafIso`: **the two spellings of `𝓕^a` on the
  big fppf site of `S` agree as abelian sheaves**, in every degree — the positive-degree
  counterpart of `AlgebraicGeometry.BigFppfOver.hZeroBaseAssociatedModuleAddEquiv`.
* `AlgebraicGeometry.BigFppfOver.zariskiClause2Map`: the canonical map
  `g^*(𝒢|_{S_Zar}) ⟶ 𝒢|_{X_Zar}` of clause (2), the base-change map of the square formed by
  `f_big`, the two restrictions to small Zariski sites and `g`; under clause (1) it is the
  identification `g^*(𝒢|_{S_Zar}) ≅ ℱ|_{X_Zar}` of
  `AlgebraicGeometry.BigFppfOver.zariskiComparisonRestrictIso` followed by the restriction of
  `φ`, by `AlgebraicGeometry.BigFppfOver.zariskiClause2Map_eq`.
* `AlgebraicGeometry.BigFppfOver.comparisonStepSiteAddEquiv`: the 0755 step read at the terminal
  object, `H^p((Sch/S)_fppf, ℱ) ≅ H^p((Sch/S)_fppf, 𝒢)`.

## Main results

* `AlgebraicGeometry.BigFppfOver.zariskiSmallSiteCohomologyAddEquiv`: **the conclusion of
  [Stacks, Tag 0756] at `U = S` and `τ = Zar`**, from clauses (1) and (2) and nothing else.
* `AlgebraicGeometry.BigFppfOver.smallZariskiSiteCohomologyAddEquiv`: the same with the
  right-hand side read on the small Zariski site of [Stacks, Tag 020T] (2).
* `AlgebraicGeometry.BigFppfOver.isQuasicoherent_objZariskiRestrict`: clause (2) at an object `T`
  makes `𝒢|_{X_Zar}` quasi-coherent, `X` being the scheme of `T` — clause (1) of 0756 for the
  restricted sheaf.

## Why nothing here carries the tag, and what the tag's own declarations are

**No `@[stacks 0756]` attribute is placed here.**  The tag concludes
`H^p(U, 𝒢) = H^p(U, 𝒢|_{U_Zar})` for *every* `U` flat and locally of finite presentation over
`S`; what is proved below is the instance `U = S`, which is narrower, and registering it would be
the over-claim the repository rejects elsewhere (compare the note on
`AlgebraicGeometry.BigFppfOver.associatedModuleIsoSections`, untagged because a statement about
one topology is narrower than a clause quantifying over five).

The passage from `U = S` to a general `U` is the reduction of this file run in the other
direction:
write `X` for the scheme of `U` and `𝒢_U = (objRestrict B S hS U).obj 𝒢` for the restriction of
`𝒢` to `(Sch/X)_fppf`, and apply
`AlgebraicGeometry.BigFppfOver.zariskiSmallSiteCohomologyAddEquiv` at the base `X` to `𝒢_U`.  Its
two hypotheses there are clause (1) and clause (2) for `𝒢_U` over `X`: the first is
`AlgebraicGeometry.BigFppfOver.isQuasicoherent_objZariskiRestrict` below and the second is
`AlgebraicGeometry.BigFppfOver.isIso_zariskiClause2Map_objRestrict`.  Both are proved, and the
general-`U` conclusion they give is
`AlgebraicGeometry.BigFppfOver.flatSmallSiteCohomologyAddEquiv`
(`StacksFrontier/AlgebraicGeometry/Descent/Parasitic/FlatCohomologyGeneralBase.lean`), which is
where the tag is registered at `τ = Zariski`.  At `τ = étale` it is
`AlgebraicGeometry.BigFppfOver.flatSmallEtaleSiteCohomologyAddEquiv`
(`StacksFrontier/AlgebraicGeometry/Descent/Parasitic/FlatCohomologyEtaleConclusion.lean`), whose
clause (2) is `AlgebraicGeometry.BigFppfOver.etaleClause2Map`.

## Implementation notes

The canonical map of clause (2) is defined through the comparison of inverse images of the square
of ringed sites, as the unit of the associated-module adjunction of `X`, the comparison of
[Stacks, Tag 03DV] and the restriction of the counit `φ`.  That this is the adjoint transpose of
the restriction map `𝒢|_{S_Zar} ⟶ g_*(𝒢|_{X_Zar})`, the source's description, is
`AlgebraicGeometry.BigFppfOver.zariskiClause2Map_eq_homEquiv_symm`
(`StacksFrontier/AlgebraicGeometry/Descent/Parasitic/FlatCohomologyBaseChangeFactor.lean`).  The
definition needs no hypothesis on `𝒢`; clause (1) enters only through
`AlgebraicGeometry.BigFppfOver.zariskiClause2Map_eq`, which makes its first two factors an
isomorphism and so reduces clause (2) to the invertibility of the restriction of `φ`.

## References

* [Stacks Project, Tag 0756](https://stacks.math.columbia.edu/tag/0756)
* [Stacks Project, Tag 0755](https://stacks.math.columbia.edu/tag/0755)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03P2](https://stacks.math.columbia.edu/tag/03P2)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03FH](https://stacks.math.columbia.edu/tag/03FH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.TerminalCohomology
open scoped AlgebraicGeometry

universe w v u

namespace Stacks.Cohomology

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{v}] [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]

/-- **Isomorphic abelian sheaves have the same cohomology.**  `CategoryTheory.Sheaf.H.map` at
the two directions of the isomorphism are mutually inverse, by functoriality. -/
public def hAddEquivOfIso {X Y : Sheaf J AddCommGrpCat.{v}} (e : X ≅ Y) (n : ℕ) :
    Sheaf.H.{w} X n ≃+ Sheaf.H.{w} Y n where
  toFun := Sheaf.H.map e.hom n
  invFun := Sheaf.H.map e.inv n
  left_inv _ := by rw [← Sheaf.H.map_comp_apply, e.hom_inv_id, Sheaf.H.map_id_apply]
  right_inv _ := by rw [← Sheaf.H.map_comp_apply, e.inv_hom_id, Sheaf.H.map_id_apply]
  map_add' _ _ := by simp

end Stacks.Cohomology

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The two spellings of `𝓕^a` on the big fppf site -/

/-- **The two spellings of `𝓕^a` on `(Sch/S)_fppf` agree, as abelian sheaves and in every
degree.**  For a quasi-coherent `𝒪_S`-module `𝓕`, the abelian sheaf
`AlgebraicGeometry.bigOverAssociatedSheaf` that [Stacks, Tag 03DW] clause (1) is stated for is
the abelian sheaf underlying the pullback
`AlgebraicGeometry.BigFppfOver.associatedModule` that the comparison pair of
[Stacks, Tag 0756] is built from.

Two steps, both already in the tree.  The sections-defined `𝓕^a` of [Stacks, Tag 03DU] (3) is
the pullback by [Stacks, Remark 03FH] (1),
`AlgebraicGeometry.BigFppfOver.associatedModuleIsoOverAssociatedModule`; and the abelian sheaf
underlying it is `AlgebraicGeometry.bigOverAssociatedSheaf` by `rfl`, because
`AlgebraicGeometry.overTopology` at `τ = fppf` is
`AlgebraicGeometry.BigFppfOver.topology`, `AlgebraicGeometry.overToSlice` at `τ = fppf` is
`CategoryTheory.Over.post B.inclusion`, and the sheaf conditions are propositions.

This is the positive-degree counterpart of
`AlgebraicGeometry.BigFppfOver.hZeroBaseAssociatedModuleAddEquiv`, which identifies the degree-
zero cohomology of the two and carries `@[stacks 03DW]`.  It carries no attribute: 03DW is a
statement about cohomology, and this is an identification of the coefficients it is taken in. -/
public def bigOverAssociatedSheafIso (F : S.Modules) [F.IsQuasicoherent] :
    bigOverAssociatedSheaf S F .fppf B hS ≅
      (SheafOfModules.toSheaf (structureSheaf B S hS)).obj ((associatedModule B S hS).obj F) :=
  ((SheafOfModules.toSheaf (structureSheaf B S hS)).mapIso
    (associatedModuleIsoOverAssociatedModule B S hS F)).symm

/-! ### The terminal object is flat and locally of finite presentation -/

/-- The terminal object `(⊤ ↪ S) → S` of `(Sch/S)_fppf` is flat over `S`: its structure morphism
is the inclusion of the open `⊤`. -/
public theorem flat_opensObjTop :
    Flat ((Over.post B.inclusion).obj (opensObj B S hS ⊤)).hom :=
  inferInstanceAs (Flat (⊤ : S.Opens).ι)

/-- The terminal object `(⊤ ↪ S) → S` of `(Sch/S)_fppf` is locally of finite presentation over
`S`: its structure morphism is the inclusion of the open `⊤`. -/
public theorem locallyOfFinitePresentation_opensObjTop :
    LocallyOfFinitePresentation ((Over.post B.inclusion).obj (opensObj B S hS ⊤)).hom :=
  inferInstanceAs (LocallyOfFinitePresentation (⊤ : S.Opens).ι)

/-! ### Clause (2) of the source -/

section Clause

variable (T : BigFppfOver B S hS) (G : SheafOfModules.{u} (structureSheaf B S hS))

/-- **The canonical map `g^*_{Zar, small}(𝒢|_{S_Zar}) ⟶ 𝒢|_{X_Zar}` of clause (2) of
[Stacks, Tag 0756]**, for `g : X ⟶ S` the structure morphism of an object `T` of
`(Sch/S)_fppf`.

It is the base-change map of the square of ringed sites formed by `f_big : (Sch/X)_fppf ⟶
(Sch/S)_fppf`, the two restrictions to small Zariski sites and `g`: the unit of the
associated-module adjunction of `X` at `g^*(𝒢|_{S_Zar})`, the comparison of inverse images
`(g^*(-))^a ≅ (-)^a|_{(Sch/X)_fppf}` of [Stacks, Tag 03DV], and the restriction of the counit
`φ : (𝒢|_{S_Zar})^a ⟶ 𝒢`.  `AlgebraicGeometry.BigFppfOver.zariskiClause2Map_eq_homEquiv_symm`
identifies it with the adjoint transpose of `𝒢|_{S_Zar} ⟶ g_*(𝒢|_{X_Zar})`, restriction along
the base change `X ×_S V ⟶ V` followed by the identification of the two composite direct
images, which is the source's description.  No hypothesis on `𝒢` is needed to define it. -/
public def zariskiClause2Map :
    (Scheme.Modules.pullback (objHom B S hS T)).obj ((restrictModule B S hS).obj G) ⟶
      objZariskiRestrict B S hS T G :=
  ((associatedModuleAdjunction B (objScheme B S hS T) (contains_objScheme B S hS T)).unit.app
      ((Scheme.Modules.pullback (objHom B S hS T)).obj ((restrictModule B S hS).obj G)) ≫
    (restrictModule B (objScheme B S hS T) (contains_objScheme B S hS T)).map
      ((associatedModuleObjRestrictNatIso B S hS T).hom.app ((restrictModule B S hS).obj G))) ≫
    (restrictModule B (objScheme B S hS T) (contains_objScheme B S hS T)).map
      ((objRestrict B S hS T).map (zariskiComparisonMap B S hS G))

/-- **Under clause (1) the canonical map of clause (2) is an isomorphism followed by the
restriction of `φ`**: its first two factors are
`AlgebraicGeometry.BigFppfOver.zariskiComparisonRestrictIso`, the identification
`g^*(𝒢|_{S_Zar}) ≅ ℱ|_{X_Zar}` for `ℱ = (𝒢|_{S_Zar})^a`. -/
public theorem zariskiClause2Map_eq
    (h : SheafOfModules.IsQuasicoherent (R := S.ringCatSheaf)
      ((restrictModule B S hS).obj G)) :
    zariskiClause2Map B S hS T G =
      (zariskiComparisonRestrictIso B S hS T G h).hom ≫
        (restrictModule B (objScheme B S hS T) (contains_objScheme B S hS T)).map
          ((objRestrict B S hS T).map (zariskiComparisonMap B S hS G)) :=
  rfl

/-- **Clause (2) of [Stacks, Tag 0756] gives the hypothesis of the comparison step.**  If the
canonical map of clause (2) is an isomorphism at `T`, so is the restriction of the comparison map
`φ` to the small Zariski site of the scheme of `T`: the first factor of
`AlgebraicGeometry.BigFppfOver.zariskiClause2Map` is an isomorphism already. -/
public theorem isIso_objZariskiRestrict_map_zariskiComparisonMap
    (h : SheafOfModules.IsQuasicoherent (R := S.ringCatSheaf)
      ((restrictModule B S hS).obj G))
    (h2 : IsIso (zariskiClause2Map B S hS T G)) :
    IsIso ((restrictModule B (objScheme B S hS T) (contains_objScheme B S hS T)).map
      ((objRestrict B S hS T).map (zariskiComparisonMap B S hS G))) :=
  @IsIso.of_isIso_comp_left _ _ _ _ _ (zariskiComparisonRestrictIso B S hS T G h).hom
    ((restrictModule B (objScheme B S hS T) (contains_objScheme B S hS T)).map
      ((objRestrict B S hS T).map (zariskiComparisonMap B S hS G))) inferInstance h2

/-- **Clause (1) of [Stacks, Tag 0756] for the restricted sheaf.**  If the canonical map of
clause (2) is an isomorphism at `T`, then `𝒢|_{X_Zar}` is quasi-coherent for `X` the scheme of
`T`: it is then isomorphic to `g^*(𝒢|_{S_Zar})`, which is quasi-coherent by [Stacks, Tag 01BG].

This is the hypothesis (1) that
`AlgebraicGeometry.BigFppfOver.zariskiSmallSiteCohomologyAddEquiv` would need at the base `X` in
order to give the conclusion of 0756 over a general `U`; see the module documentation for the
one hypothesis that is still missing there. -/
public theorem isQuasicoherent_objZariskiRestrict
    (h : SheafOfModules.IsQuasicoherent (R := S.ringCatSheaf)
      ((restrictModule B S hS).obj G))
    (h2 : IsIso (zariskiClause2Map B S hS T G)) :
    SheafOfModules.IsQuasicoherent (R := (objScheme B S hS T).ringCatSheaf)
      (objZariskiRestrict B S hS T G) :=
  ObjectProperty.prop_of_iso
    (SheafOfModules.isQuasicoherent (objScheme B S hS T).ringCatSheaf)
    (@asIso _ _ _ _ _ h2)
    (Stacks.Modules.isQuasicoherent_pullback (objHom B S hS T)
      ((restrictModule B S hS).obj G) h)

end Clause

/-! ### The conclusion -/

section Main

variable (G : SheafOfModules.{u} (structureSheaf B S hS))

-- The localized big fppf site is essentially small and the Zariski site of a scheme has enough
-- injectives; without these four the `CategoryTheory.Sheaf.H` groups below are not defined.
attribute [local instance] Stacks.Topology.hasExt_sheafOpens
  Stacks.Topology.enoughInjectives_sheafOpens
  Stacks.Cohomology.FreeYonedaUnivLE.enoughInjectives_essentiallySmallSite
  Stacks.Cohomology.FreeYonedaUnivLE.hasExt_essentiallySmallSite

/-- **The comparison step of [Stacks, Tag 0756] read at the terminal object.**  For `𝒢` a sheaf
of `𝒪`-modules on `(Sch/S)_fppf`, `ℱ = (𝒢|_{S_Zar})^a` and `φ : ℱ ⟶ 𝒢` the counit, if `φ` is an
isomorphism on the small Zariski site of the scheme of every object flat and locally of finite
presentation over `S`, then

```
H^p((Sch/S)_fppf, ℱ)  ≅  H^p((Sch/S)_fppf, 𝒢)      for every p.
```

This is `AlgebraicGeometry.bigFppfCohomology_map_bijective_of_isIso_zariskiRestriction` at the
object `AlgebraicGeometry.BigFppfOver.opensObj B S hS ⊤`, which is flat and locally of finite
presentation over `S` and terminal in the site, read through
`Stacks.Cohomology.TerminalCohomology.h'AddEquivH` on both sides.  Only a bijection is
transported, so no naturality of the comparison is claimed. -/
public def comparisonStepSiteAddEquiv
    (hφ : ∀ Y : BigFppfOver B S hS,
      Flat ((Over.post B.inclusion).obj Y).hom →
      LocallyOfFinitePresentation ((Over.post B.inclusion).obj Y).hom →
      IsIso ((restrictModule B (objScheme B S hS Y) (contains_objScheme B S hS Y)).map
        ((objRestrict B S hS Y).map (zariskiComparisonMap B S hS G))))
    (p : ℕ) :
    Sheaf.H.{u} ((SheafOfModules.toSheaf (structureSheaf B S hS)).obj
        (zariskiComparisonModule B S hS G)) p ≃+
      Sheaf.H.{u} ((SheafOfModules.toSheaf (structureSheaf B S hS)).obj G) p :=
  ((h'AddEquivH (topology B S hS)
          ((SheafOfModules.toSheaf (structureSheaf B S hS)).obj
            (zariskiComparisonModule B S hS G)) p _
          (isTerminalOpensObjTop B S hS)).symm.trans
      (AddEquiv.ofBijective _
        (bigFppfCohomology_map_bijective_of_isIso_zariskiRestriction B S hS
          (zariskiComparisonMap B S hS G) hφ (opensObj B S hS ⊤)
          ⟨flat_opensObjTop B S hS, locallyOfFinitePresentation_opensObjTop B S hS⟩ p))).trans
    (h'AddEquivH (topology B S hS)
      ((SheafOfModules.toSheaf (structureSheaf B S hS)).obj G) p _
      (isTerminalOpensObjTop B S hS))

/-- **The conclusion of [Stacks, Tag 0756] at `U = S` and `τ = Zar`.**  Let `𝒢` be a sheaf of
`𝒪`-modules on `(Sch/S)_fppf` such that

1. `𝒢|_{S_Zar}` is quasi-coherent, and
2. for every object of `(Sch/S)_fppf` flat and locally of finite presentation over `S`, with
   structure morphism `g : X ⟶ S`, the canonical map `g^*(𝒢|_{S_Zar}) → 𝒢|_{X_Zar}` of
   `AlgebraicGeometry.BigFppfOver.zariskiClause2Map` is an isomorphism.

Then in every degree

```
H^p((Sch/S)_fppf, 𝒢)  ≅  H^p(S, 𝒢|_{S_Zar}).
```

The right-hand side is the cohomology of the site of opens of `S` with values in the restriction
of `𝒢` along the inclusion of the small Zariski site of `S`; see
`AlgebraicGeometry.BigFppfOver.smallZariskiSiteCohomologyAddEquiv` for the same statement with
that side read on the site `AlgebraicGeometry.SmallZariski` of [Stacks, Tag 020T] (2).

Three steps.  Clause (2) supplies the hypothesis of
`AlgebraicGeometry.BigFppfOver.comparisonStepSiteAddEquiv` through
`AlgebraicGeometry.BigFppfOver.isIso_objZariskiRestrict_map_zariskiComparisonMap`, giving
`H^p((Sch/S)_fppf, ℱ) ≅ H^p((Sch/S)_fppf, 𝒢)` for `ℱ = (𝒢|_{S_Zar})^a`; clause (1) makes
`𝒢|_{S_Zar}` quasi-coherent, so [Stacks, Tag 03DW] clause (1) —
`AlgebraicGeometry.bigOverQuasiCoherentSiteCohomologyAddEquiv` — gives
`H^p(S, 𝒢|_{S_Zar}) ≅ H^p((Sch/S)_fppf, 𝓕^a)` in the sections spelling of `𝓕^a`; and
`AlgebraicGeometry.BigFppfOver.bigOverAssociatedSheafIso` identifies that with `ℱ`.

**No `@[stacks 0756]` attribute**: the tag's conclusion is for every `U` flat and locally of
finite presentation over `S`, and this is the instance `U = S`.  The general `U` is
`AlgebraicGeometry.BigFppfOver.flatSmallSiteCohomologyAddEquiv`, which applies this statement at
the base `X` to `𝒢|_{(Sch/X)_fppf}` and carries the tag. -/
public def zariskiSmallSiteCohomologyAddEquiv
    (hqc : SheafOfModules.IsQuasicoherent (R := S.ringCatSheaf)
      ((restrictModule B S hS).obj G))
    (hcl2 : ∀ Y : BigFppfOver B S hS,
      Flat ((Over.post B.inclusion).obj Y).hom →
      LocallyOfFinitePresentation ((Over.post B.inclusion).obj Y).hom →
      IsIso (zariskiClause2Map B S hS Y G))
    (p : ℕ) :
    Sheaf.H.{u} ((SheafOfModules.toSheaf (structureSheaf B S hS)).obj G) p ≃+
      Sheaf.H.{u} ((SheafOfModules.toSheaf S.ringCatSheaf).obj
        ((restrictModule B S hS).obj G)) p :=
  haveI : SheafOfModules.IsQuasicoherent (R := S.ringCatSheaf)
      ((restrictModule B S hS).obj G) := hqc
  (((bigOverQuasiCoherentSiteCohomologyAddEquiv S ((restrictModule B S hS).obj G) .fppf B hS
            p).trans
        (Stacks.Cohomology.hAddEquivOfIso (topology B S hS)
          (bigOverAssociatedSheafIso B S hS ((restrictModule B S hS).obj G)) p)).trans
      (comparisonStepSiteAddEquiv B S hS G
        (fun Y h1 h2 =>
          isIso_objZariskiRestrict_map_zariskiComparisonMap B S hS Y G hqc (hcl2 Y h1 h2))
        p)).symm

/-- **The conclusion of [Stacks, Tag 0756] at `U = S` and `τ = Zar`, with the right-hand side on
the small Zariski site.**  Under the hypotheses of
`AlgebraicGeometry.BigFppfOver.zariskiSmallSiteCohomologyAddEquiv`,

```
H^p((Sch/S)_fppf, 𝒢)  ≅  H^p(S_Zar, (𝒢|_{S_Zar})^a),
```

the right-hand side being the cohomology of the small Zariski site of [Stacks, Tag 020T] (2)
with values in the associated sheaf of [Stacks, Tag 03DU] (4) at `τ = Zariski`.  This is the
previous statement composed with the small Zariski link of [Stacks, Tag 03DW] clause (2),
`AlgebraicGeometry.smallZariskiQuasiCoherentSiteCohomologyAddEquiv`.

The big Zariski site `BZ` carrying `S_Zar` is unrelated to the big fppf site `B`: the
restriction `𝒢|_{S_Zar}` is produced as an `𝒪_S`-module and only then read on `S_Zar`. -/
public def smallZariskiSiteCohomologyAddEquiv (BZ : BigZariskiSite.{u}) (hSZ : BZ.Contains S)
    (hqc : SheafOfModules.IsQuasicoherent (R := S.ringCatSheaf)
      ((restrictModule B S hS).obj G))
    (hcl2 : ∀ Y : BigFppfOver B S hS,
      Flat ((Over.post B.inclusion).obj Y).hom →
      LocallyOfFinitePresentation ((Over.post B.inclusion).obj Y).hom →
      IsIso (zariskiClause2Map B S hS Y G))
    (p : ℕ) :
    Sheaf.H.{u} ((SheafOfModules.toSheaf (structureSheaf B S hS)).obj G) p ≃+
      Sheaf.H.{u} (smallZariskiAssociatedSheaf BZ S hSZ ((restrictModule B S hS).obj G)) p :=
  haveI : SheafOfModules.IsQuasicoherent (R := S.ringCatSheaf)
      ((restrictModule B S hS).obj G) := hqc
  (zariskiSmallSiteCohomologyAddEquiv B S hS G hqc hcl2 p).trans
    (smallZariskiQuasiCoherentSiteCohomologyAddEquiv BZ S hSZ
      ((restrictModule B S hS).obj G) p)

end Main

end AlgebraicGeometry.BigFppfOver

end
