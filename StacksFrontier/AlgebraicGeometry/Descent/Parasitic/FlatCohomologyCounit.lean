module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.FullyFaithfulUnconditional
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.ObjectFunctoriality
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCounit
public import StacksFrontier.AlgebraicGeometry.Descent.Parasitic.FlatCohomologySectionwiseIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FppfEtaleComparison.QuasiCoherentPullback
public import StacksCore.Tactic.StacksAttribute

/-!
# The comparison module `ℱ = (𝒢|_{S_τ})^a` and its canonical map to `𝒢`

Let `B` be a big fppf site, `S` a scheme below its cutoff and `𝒢` a sheaf of `𝒪`-modules on
`(Sch/S)_fppf`.  [Stacks, Tag 0756] proves its conclusion by comparing `𝒢` with the module
`ℱ = (𝒢|_{S_τ})^a` pulled back from the small `τ`-site of `S`, along the canonical comparison
map `φ : ℱ ⟶ 𝒢`.  This file constructs that pair, for `τ = Zariski` and for `τ = étale`, and
feeds it to the comparison step
`AlgebraicGeometry.bigFppfCohomology_map_bijective_of_isIso_sections`.

The construction is the counit of an adjunction already in the development: `ℱ` is the inverse
image of the restriction of `𝒢` along the morphism of ringed sites
`((Sch/S)_fppf, 𝒪) ⟶ (S_τ, 𝒪)`, and `φ` is the counit of the inverse-image–direct-image
adjunction at `𝒢`.  At `τ = Zariski` that adjunction is
`AlgebraicGeometry.BigFppfOver.associatedModuleAdjunction` and at `τ = étale` it is
`AlgebraicGeometry.BigFppfOver.smallEtaleToBaseModuleAdjunction` at `.fppf`, the morphism `a_S`.

## Main definitions

* `AlgebraicGeometry.BigFppfOver.zariskiComparisonModule` and
  `AlgebraicGeometry.BigFppfOver.zariskiComparisonMap`: the pair `(ℱ, φ)` at `τ = Zariski`.
* `AlgebraicGeometry.BigFppfOver.etaleComparisonModule` and
  `AlgebraicGeometry.BigFppfOver.etaleComparisonMap`: the pair `(ℱ, φ)` at `τ = étale`.

## Main results

* `AlgebraicGeometry.BigFppfOver.baseRingStructureSheaf_fppf_eq`: the fppf member of the five
  structure sheaves of `AlgebraicGeometry.FibredSite.baseRingStructureSheaf` *is* the structure
  sheaf `AlgebraicGeometry.BigFppfOver.structureSheaf` of the big fppf site over `S`, so the
  étale pair lives over the same sheaf of rings as the Zariski one and the comparison step
  applies to both without a bridge.
* `AlgebraicGeometry.BigFppfOver.isIso_restrictModule_map_zariskiComparisonMap` and
  `AlgebraicGeometry.BigFppfOver.bijective_zariskiComparisonMap_val_app_opensObj`: **clause (1)
  of [Stacks, Tag 0756] used** — if `𝒢|_{S_Zar}` is quasi-coherent then `φ` is bijective on
  sections over every open of `S`.
* `AlgebraicGeometry.BigFppfOver.zariskiComparisonRestrictIso`: **clause (1) used again, and this
  is where the source uses it** — for `f : X ⟶ S` the structure morphism of any object `T` of the
  big fppf site, `ℱ` restricted to the small Zariski site of `X` is the pullback
  `f^*(𝒢|_{S_Zar})`, so that the two sides of clause (2) become comparable.
* `AlgebraicGeometry.BigFppfOver.bigFppfCohomology_zariskiComparisonMap_bijective` and
  `AlgebraicGeometry.BigFppfOver.bigFppfCohomology_etaleComparisonMap_bijective`: for the
  *constructed* `φ`, if `φ` is an isomorphism on sections over every object flat and locally of
  finite presentation over `S` then `H^p(U, ℱ) → H^p(U, 𝒢)` is bijective for every such `U` and
  every `p`.

## Implementation notes

`AlgebraicGeometry.FibredSite.baseRingStructureSheaf B S hS .fppf` and
`AlgebraicGeometry.BigFppfOver.structureSheaf B S hS` have the same underlying presheaf by
`AlgebraicGeometry.FibredSite.baseRingStructureSheaf_obj`, and the sheaf condition is a
proposition, so the two are equal — and the localized fppf topology is literally the `.fppf`
member of the five localized topologies.  That is why `baseRingStructureSheaf_fppf_eq` is `rfl`,
and why the étale half of this file can be stated over
`AlgebraicGeometry.BigFppfOver.structureSheaf`: no transport between two structure sheaves
appears, and the instances the comparison step asks for are the ones of the big fppf site.

The clause (1) statement is the Zariski analogue of
`AlgebraicGeometry.SmallEtale.isIso_restrictModule_map_counit`, with the same two-line proof:
the unit of the adjunction is an isomorphism at a quasi-coherent module by Stacks 0GN7
(`AlgebraicGeometry.BigFppfOver.unitIsoOnQuasicoherent`), and the triangle identity exhibits the
restriction of the counit as its inverse.  Its étale counterpart is not carried out here, but
the input it needs — the unit of
`AlgebraicGeometry.BigFppfOver.smallEtaleToBaseModuleAdjunction` being an isomorphism at the
modules quasi-coherent on `S_étale` — exists, as
`AlgebraicGeometry.BigFppfOver.isIso_smallEtaleToBaseUnit_app`
(`StacksFrontier/AlgebraicGeometry/EtaleCohomology/FppfEtaleComparison/SmallEtaleToBaseUnit.lean`).

**What this file does and does not add to [Stacks, Tag 0756].**  Of the three pieces the source's
proof needs beyond the comparison step, this file supplies the first:

1. The construction of `ℱ = (𝒢|_{S_τ})^a` together with its canonical comparison map `φ : ℱ ⟶ 𝒢`
   — **supplied here**, at both `τ = Zariski` and `τ = étale`, so that the comparison step is
   applied to the development's own canonical morphism rather than to an arbitrary one.
2. The derivation of the sectionwise hypothesis from clauses (1) and (2) of the source.
   Clause (2) says that `g^*_{τ,small}(𝒢|_{S_τ}) → 𝒢|_{U_τ}` is an isomorphism for every flat,
   locally finitely presented `g : U → S`; read at the identity chart of `U_τ` that is exactly
   the hypothesis `IsIso (φ.val.app (op U))` carried below.  Making that reading formal needs
   three things.

   * The two sides of clause (2) have to be comparable: its left-hand side `g^*(𝒢|_{S_Zar})` has
     to be identified with something built from `ℱ`.  That is
     `AlgebraicGeometry.BigFppfOver.zariskiComparisonRestrictIso`, **supplied here**, and it is
     where clause (1) does its work — `g^*(𝒢|_{S_Zar})` is quasi-coherent by Stacks 01BG, so the
     unit of the associated-module adjunction over `U` is an isomorphism at it, and Stacks 03DV
     functorial in the object turns that into `ℱ|_{U_Zar} ≅ g^*(𝒢|_{S_Zar})`.
   * The canonical map of clause (2) itself, `AlgebraicGeometry.BigFppfOver.zariskiClause2Map`,
     the base-change map of the square of ringed sites, and its identification with the
     adjoint transpose of the restriction map `𝒢|_{S_Zar} ⟶ g_*(𝒢|_{U_Zar})`,
     `AlgebraicGeometry.BigFppfOver.zariskiClause2Map_eq_homEquiv_symm`; at `τ = étale` these are
     `AlgebraicGeometry.BigFppfOver.etaleClause2Map` and
     `AlgebraicGeometry.BigFppfOver.etaleClause2Map_eq_homEquiv_symm`.
   * That this map factors as `zariskiComparisonRestrictIso` followed by the restriction of `φ` to
     `U_Zar`, which is `AlgebraicGeometry.BigFppfOver.zariskiClause2Map_eq`.

   With these the sectionwise hypothesis is derived from clauses (1) and (2), in
   `StacksFrontier/AlgebraicGeometry/Descent/Parasitic/FlatCohomologySmallSiteComparison.lean`.
3. The identification `H^p(U, ℱ) = H^p(U, 𝒢|_{U_τ})` by [Stacks, Tag 03DW] — **not supplied**,
   and this is the remaining substance of the tag.  03DW itself is available in every degree
   (`AlgebraicGeometry.bigOverQuasiCoherentGlobalCohomologyIso` for clause (1),
   `AlgebraicGeometry.smallEtaleQuasiCoherentGlobalCohomologyIso` and
   `AlgebraicGeometry.smallZariskiQuasiCoherentGlobalCohomologyIso` for clause (2)), but all
   three compare cohomology **at the base scheme**, whereas 0756 needs the comparison at an
   arbitrary object `U` of the big site.  Getting there needs the localization of big-site
   cohomology at an object instantiated at the structure sheaf of a big fppf site — the abstract
   form is `Stacks.Cohomology.OverObjectCohomology.h'AddEquivHOver` and the fibred-category form
   `AlgebraicGeometry.Stack.cohomologyOverObjectIso` ([Stacks, Tag 075F]) — together with the
   base change `(g^*𝓕)^a ≅ (𝓕^a)|_{(Sch/U)_fppf}`
   (`AlgebraicGeometry.BigFppfOver.associatedModuleBaseChangeIso`, [Stacks, Tag 03LC]) and 03DW
   read at `U`.

   **At `U = S` none of that is needed, and the conclusion is asserted.**
   `AlgebraicGeometry.BigFppfOver.zariskiSmallSiteCohomologyAddEquiv`
   (`StacksFrontier/AlgebraicGeometry/Descent/Parasitic/FlatCohomologySmallSiteComparison.lean`)
   proves `H^p((Sch/S)_fppf, 𝒢) ≅ H^p(S, 𝒢|_{S_Zar})` in every degree from clauses
   (1) and (2).  Reading "cohomology over `T`" as the statement of record for Stacks 0756 does —
   the global cohomology of the restriction to the big fppf site of `T` — the case `U = S`
   takes place entirely at the terminal object of the site, where `Sheaf.H'` and `Sheaf.H` agree,
   so neither 075F nor a base change enters.  The `𝓕^a` bridge that the two halves meet at is
   `AlgebraicGeometry.BigFppfOver.bigOverAssociatedSheafIso` there, from
   `AlgebraicGeometry.BigFppfOver.associatedModuleIsoOverAssociatedModule` and
   `AlgebraicGeometry.BigFppfOver.overAssociatedModule_fppf`.  Still open: a general `U`, for
   which that file states the single missing hypothesis, and `τ = étale`.

## References

* [Stacks Project, Tag 0756](https://stacks.math.columbia.edu/tag/0756)
* [Stacks Project, Tag 0755](https://stacks.math.columbia.edu/tag/0755)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
* [Stacks Project, Tag 0GN7](https://stacks.math.columbia.edu/tag/0GN7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry.BigFppfOver

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The fppf member of the five structure sheaves of
`AlgebraicGeometry.FibredSite.baseRingStructureSheaf` is the structure sheaf of the big fppf site
over `S`: the underlying presheaves agree and the sheaf condition is a proposition. -/
public theorem baseRingStructureSheaf_fppf_eq :
    FibredSite.baseRingStructureSheaf B S hS .fppf = structureSheaf B S hS := rfl

/-! ### The comparison pair at `τ = Zariski` -/

/-- **`ℱ = (𝒢|_{S_Zar})^a`.**  The associated module of the restriction of `𝒢` along the
inclusion of the small Zariski site of `S`, that is, the inverse image of `𝒢|_{S_Zar}` along the
morphism of ringed sites `((Sch/S)_fppf, 𝒪) ⟶ (S_Zar, 𝒪_S)`.  This is the `ℱ` of
[Stacks, Tag 0756] at `τ = Zar`. -/
public def zariskiComparisonModule (G : SheafOfModules.{u} (structureSheaf B S hS)) :
    SheafOfModules.{u} (structureSheaf B S hS) :=
  (associatedModule B S hS).obj ((restrictModule B S hS).obj G)

/-- **The canonical comparison map `φ : (𝒢|_{S_Zar})^a ⟶ 𝒢`**, the counit of the
associated-module adjunction at `𝒢`.  This is the `φ` of [Stacks, Tag 0756] at `τ = Zar`. -/
public def zariskiComparisonMap (G : SheafOfModules.{u} (structureSheaf B S hS)) :
    zariskiComparisonModule B S hS G ⟶ G :=
  (associatedModuleAdjunction B S hS).counit.app G

/-- The comparison map at `τ = Zar` is the counit of the associated-module adjunction. -/
public theorem zariskiComparisonMap_eq (G : SheafOfModules.{u} (structureSheaf B S hS)) :
    zariskiComparisonMap B S hS G = (associatedModuleAdjunction B S hS).counit.app G := rfl

/-- **Clause (1) of [Stacks, Tag 0756], used: the restriction of `φ` to the small Zariski site is
an isomorphism.**  If `𝒢|_{S_Zar}` is quasi-coherent then the unit of the associated-module
adjunction at it is an isomorphism by Stacks 0GN7, and the triangle identity exhibits the
restriction of `φ` as its inverse. -/
public theorem isIso_restrictModule_map_zariskiComparisonMap
    (G : SheafOfModules.{u} (structureSheaf B S hS))
    (h : SheafOfModules.IsQuasicoherent (R := S.ringCatSheaf)
      ((restrictModule B S hS).obj G)) :
    IsIso ((restrictModule B S hS).map (zariskiComparisonMap B S hS G)) := by
  have hu : IsIso ((associatedModuleAdjunction B S hS).unit.app
      ((restrictModule B S hS).obj G)) :=
    unitIsoOnQuasicoherent B S hS ⟨(restrictModule B S hS).obj G, h⟩
  have htri : (associatedModuleAdjunction B S hS).unit.app
      ((restrictModule B S hS).obj G) ≫
      (restrictModule B S hS).map (zariskiComparisonMap B S hS G) = 𝟙 _ :=
    (associatedModuleAdjunction B S hS).right_triangle_components G
  have hcomp : IsIso ((associatedModuleAdjunction B S hS).unit.app
      ((restrictModule B S hS).obj G) ≫
      (restrictModule B S hS).map (zariskiComparisonMap B S hS G)) := by
    rw [htri]
    infer_instance
  exact @IsIso.of_isIso_comp_left _ _ _ _ _
    ((associatedModuleAdjunction B S hS).unit.app ((restrictModule B S hS).obj G))
    ((restrictModule B S hS).map (zariskiComparisonMap B S hS G)) hu hcomp

/-- **Clause (1) of [Stacks, Tag 0756], used: `φ` is bijective on sections over every open of
`S`.**  Over the object of the big fppf site attached to an open `V` of `S` the comparison map is
the sectionwise inverse of the unit of the adjunction, by
`AlgebraicGeometry.BigFppfOver.isIso_restrictModule_map_zariskiComparisonMap`.

This is **not** the hypothesis the comparison step needs: that one asks for bijectivity over
every object flat and locally of finite presentation over `S`, and an open of `S` is only the
special case of an open immersion. -/
public theorem bijective_zariskiComparisonMap_val_app_opensObj
    (G : SheafOfModules.{u} (structureSheaf B S hS))
    (h : SheafOfModules.IsQuasicoherent (R := S.ringCatSheaf)
      ((restrictModule B S hS).obj G)) (V : S.Opens) :
    Function.Bijective ((zariskiComparisonMap B S hS G).val.app
      (op ((opensToBig B S hS).obj V))) :=
  SheafOfModules.bijective_val_app_of_isIso
    ((restrictModule B S hS).map (zariskiComparisonMap B S hS G))
    (isIso_restrictModule_map_zariskiComparisonMap B S hS G h) (op V)

/-! ### The comparison pair at `τ = étale` -/

/-- **`ℱ = (𝒢|_{S_étale})^a`.**  The inverse image along `a_S : ((Sch/S)_fppf, 𝒪) ⟶ (S_étale, 𝒪)`
of the restriction of `𝒢` to the small étale site of `S`.  This is the `ℱ` of
[Stacks, Tag 0756] at `τ = étale`. -/
public def etaleComparisonModule (G : SheafOfModules.{u} (structureSheaf B S hS)) :
    SheafOfModules.{u} (structureSheaf B S hS) :=
  (smallEtaleToBaseModulePullback B S hS .fppf).obj
    ((smallEtaleToBasePushforward B S hS .fppf).obj G)

/-- **The canonical comparison map `φ : (𝒢|_{S_étale})^a ⟶ 𝒢`**, the counit at `𝒢` of the
adjunction `a_S^* ⊣ a_{S,*}`.  This is the `φ` of [Stacks, Tag 0756] at `τ = étale`. -/
public def etaleComparisonMap (G : SheafOfModules.{u} (structureSheaf B S hS)) :
    etaleComparisonModule B S hS G ⟶ G :=
  (smallEtaleToBaseModuleAdjunction B S hS .fppf).counit.app G

/-- The comparison map at `τ = étale` is the counit of `a_S^* ⊣ a_{S,*}`. -/
public theorem etaleComparisonMap_eq (G : SheafOfModules.{u} (structureSheaf B S hS)) :
    etaleComparisonMap B S hS G =
      (smallEtaleToBaseModuleAdjunction B S hS .fppf).counit.app G := rfl

/-! ### Restriction of the comparison pair to the small Zariski site of an object -/

section ObjRestrict

variable (T : AlgebraicGeometry.BigFppfOver B S hS)
  (G : SheafOfModules.{u} (structureSheaf B S hS))

/-- **`𝒢|_{X_Zar}` for `X` the scheme of an object `T` of the big fppf site**: restrict `𝒢` to
the big fppf site of `X` and then along the inclusion of the small Zariski site of `X`.  This is
the right-hand side of clause (2) of [Stacks, Tag 0756] at `τ = Zar`. -/
public abbrev objZariskiRestrict : (objScheme B S hS T).Modules :=
  (restrictModule B (objScheme B S hS T) (contains_objScheme B S hS T)).obj
    ((objRestrict B S hS T).obj G)

/-- **The restriction of `ℱ = (𝒢|_{S_Zar})^a` to the small Zariski site of the scheme `X` of an
object `T` is the pullback `f^*(𝒢|_{S_Zar})` along the structure morphism `f : X ⟶ S` of `T`**,
whenever `𝒢|_{S_Zar}` is quasi-coherent — that is, under clause (1) of [Stacks, Tag 0756].

Two steps.  `f^*(𝒢|_{S_Zar})` is quasi-coherent by Stacks 01BG
(`Stacks.Modules.isQuasicoherent_pullback`), so the unit of the associated-module adjunction of
the big fppf site of `X` is an isomorphism at it by Stacks 0GN7
(`AlgebraicGeometry.BigFppfOver.unitIsoOnQuasicoherent`), identifying `f^*(𝒢|_{S_Zar})` with the
small Zariski restriction of `(f^*(𝒢|_{S_Zar}))^a`.  And `(f^*(𝒢|_{S_Zar}))^a` is `ℱ` restricted
to the big fppf site of `X` by Stacks 03DV functorial in the object,
`AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictNatIso`.

This is where clause (1) does its work in the source's derivation of the sectionwise hypothesis
from clauses (1) and (2): it makes the two sides of clause (2) comparable, the left-hand side
`f^*(𝒢|_{S_Zar})` being the small Zariski restriction of `ℱ`.  Followed by the restriction of `φ`
it is the canonical map of clause (2), `AlgebraicGeometry.BigFppfOver.zariskiClause2Map`. -/
public def zariskiComparisonRestrictIso
    (h : SheafOfModules.IsQuasicoherent (R := S.ringCatSheaf)
      ((restrictModule B S hS).obj G)) :
    (Scheme.Modules.pullback (objHom B S hS T)).obj ((restrictModule B S hS).obj G) ≅
      objZariskiRestrict B S hS T (zariskiComparisonModule B S hS G) :=
  letI hM := Stacks.Modules.isQuasicoherent_pullback (objHom B S hS T)
    ((restrictModule B S hS).obj G) h
  letI : IsIso ((associatedModuleAdjunction B (objScheme B S hS T)
      (contains_objScheme B S hS T)).unit.app
      ((Scheme.Modules.pullback (objHom B S hS T)).obj ((restrictModule B S hS).obj G))) :=
    unitIsoOnQuasicoherent B (objScheme B S hS T) (contains_objScheme B S hS T) ⟨_, hM⟩
  asIso ((associatedModuleAdjunction B (objScheme B S hS T)
      (contains_objScheme B S hS T)).unit.app
      ((Scheme.Modules.pullback (objHom B S hS T)).obj ((restrictModule B S hS).obj G))) ≪≫
    (restrictModule B (objScheme B S hS T) (contains_objScheme B S hS T)).mapIso
      ((associatedModuleObjRestrictNatIso B S hS T).app ((restrictModule B S hS).obj G))

end ObjRestrict

/-! ### The comparison step at the constructed morphism -/

section Cohomology

variable [HasSheafify (AlgebraicGeometry.BigFppfOver.topology B S hS) AddCommGrpCat.{u}]
  [(AlgebraicGeometry.BigFppfOver.topology B S hS).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasExt.{w} (Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) AddCommGrpCat.{u})]

/-- **Cohomology comparison along the counit of the associated-module adjunction at
`τ = Zar`.**  Let `ℱ = (𝒢|_{S_Zar})^a` and let `φ : ℱ ⟶ 𝒢` be the counit of the
associated-module adjunction.  If `φ` is an isomorphism on sections over every object flat and
locally of finite presentation over `S`, then

  `H^p(U, ℱ) → H^p(U, 𝒢)`

is bijective for every such `U` and every `p`.

This is `AlgebraicGeometry.bigFppfCohomology_map_bijective_of_isIso_sections` with the comparison
pair of [Stacks, Tag 0756] substituted for the arbitrary morphism there.  The conclusion of 0756
itself, the identification of the left-hand side with the small-site cohomology
`H^p(U, 𝒢|_{U_Zar})`, is established at `U = S` by
`AlgebraicGeometry.BigFppfOver.zariskiSmallSiteCohomologyAddEquiv`
(`StacksFrontier.AlgebraicGeometry.Descent.Parasitic.FlatCohomologySmallSiteComparison`). -/
public theorem bigFppfCohomology_zariskiComparisonMap_bijective
    (G : SheafOfModules.{u} (structureSheaf B S hS))
    (hφ : ∀ Y : AlgebraicGeometry.BigFppfOver B S hS,
      Flat ((Over.post B.inclusion).obj Y).hom →
      LocallyOfFinitePresentation ((Over.post B.inclusion).obj Y).hom →
      IsIso ((zariskiComparisonMap B S hS G).val.app (op Y)))
    (U : AlgebraicGeometry.BigFppfOver B S hS)
    (hU : Flat ((Over.post B.inclusion).obj U).hom ∧
      LocallyOfFinitePresentation ((Over.post B.inclusion).obj U).hom) (p : ℕ) :
    Function.Bijective
      (Stacks.Cohomology.LongExactSequence.map.{w}
        ((SheafOfModules.toSheaf (structureSheaf B S hS)).map
          (zariskiComparisonMap B S hS G)) p U) :=
  bigFppfCohomology_map_bijective_of_isIso_sections B S hS
    (zariskiComparisonMap B S hS G) hφ U hU p

/-- **Cohomology comparison along the counit of `a_S^* ⊣ a_{S,*}` at `τ = étale`.**  The same
statement as `AlgebraicGeometry.BigFppfOver.bigFppfCohomology_zariskiComparisonMap_bijective`
with `ℱ = (𝒢|_{S_étale})^a` and `φ` the counit of `a_S^* ⊣ a_{S,*}`: if `φ` is an isomorphism
on sections over every object flat and locally of finite presentation over `S`, then
`H^p(U, ℱ) → H^p(U, 𝒢)` is bijective for every such `U` and every `p`.

The module documentation records how the sectionwise hypothesis is reached at `τ = Zar`, through
`AlgebraicGeometry.BigFppfOver.isIso_restrictModule_map_zariskiComparisonMap`, and what the
étale analogue of that argument would need. -/
public theorem bigFppfCohomology_etaleComparisonMap_bijective
    (G : SheafOfModules.{u} (structureSheaf B S hS))
    (hφ : ∀ Y : AlgebraicGeometry.BigFppfOver B S hS,
      Flat ((Over.post B.inclusion).obj Y).hom →
      LocallyOfFinitePresentation ((Over.post B.inclusion).obj Y).hom →
      IsIso ((etaleComparisonMap B S hS G).val.app (op Y)))
    (U : AlgebraicGeometry.BigFppfOver B S hS)
    (hU : Flat ((Over.post B.inclusion).obj U).hom ∧
      LocallyOfFinitePresentation ((Over.post B.inclusion).obj U).hom) (p : ℕ) :
    Function.Bijective
      (Stacks.Cohomology.LongExactSequence.map.{w}
        ((SheafOfModules.toSheaf (structureSheaf B S hS)).map
          (etaleComparisonMap B S hS G)) p U) :=
  bigFppfCohomology_map_bijective_of_isIso_sections B S hS
    (etaleComparisonMap B S hS G) hφ U hU p

end Cohomology

end AlgebraicGeometry.BigFppfOver

end
