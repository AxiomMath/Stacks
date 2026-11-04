module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.BigSiteQuasiCoherentCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.SmallEtaleQuasiCoherentCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.Basic
public import StacksFrontier.AlgebraicGeometry.Topologies.FpqcQuasicoherentCore
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.CohomologyAtTheTerminalObject
public import StacksFrontier.Cotangent.CohomologyPresheaf.BiggerSiteObjectwise

/-!
# Cohomology of a quasi-coherent module over an arbitrary object of the site, proved

Let `S` be a scheme, `F` a quasi-coherent `𝒪_S`-module and `𝒞` a site of schemes over `S`.
[Stacks, Tag 03P2] compares the Zariski cohomology of `F` on `S` with the `τ`-cohomology of the
associated sheaf `Fᵃ` of [Stacks, Tag 03OG], the right-hand side being cohomology over the
object `S` of `𝒞`.  This file is [Stacks, Tag 03P3], the remark on that theorem, which has two
assertions.

This file proves both assertions with nothing carried.  The older reduction
`Stacks.EtaleCohomology.QcohSiteCohomology.zariskiCohomologyIsoCohomologyAtObject`, in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.QuasiCoherentSheaves.CohomologyAtAnObject`,
takes Theorem 03P2 at a final object as the hypothesis `h03P2`, and is left as it is.

**First assertion.**  `S` is a final object of `𝒞`, so the groups on the right-hand side of
Tag 03P2 are the right derived functors of the global sections functor of `𝒞`, that is Mathlib's
`CategoryTheory.Sheaf.H`.  One carrier per case of Tag 03P2:
`AlgebraicGeometry.bigOverAssociatedSheafGlobalCohomologyIso` for `𝒞 = (Sch/S)_τ`, with `τ` a
bound variable so that the one declaration covers all five of fppf, syntomic, smooth, étale and
Zariski, and `AlgebraicGeometry.smallEtaleAssociatedSheafGlobalCohomologyIso` for `𝒞 = S_étale`.
The final objects are `AlgebraicGeometry.isTerminal_opensBelowToOver_top` and
`AlgebraicGeometry.isTerminal_opensToEtale_top`, which are exactly the objects the two library
forms of Tag 03P2 take their right-hand sides over.

**Second assertion.**  "In fact the proof shows that `H^p(U, f^*F) = H^p_τ(U, Fᵃ)` for any object
`f : U → S` of the site."  One carrier per case of Tag 03P2 again.  For `𝒞 = (Sch/S)_τ` it is
`AlgebraicGeometry.bigOverQuasiCoherentCohomologyIsoAtObject`: for an **arbitrary** object `Z` of
a localized big `τ`-site of `S`, with underlying scheme `Z.left.obj` and structure morphism
`Z.hom.hom : Z.left.obj ⟶ S`,

  `H^p(Z.left.obj, Z.hom.hom^* F) ≅ H^p_τ(Z, Fᵃ)`.

For `𝒞 = S_étale` it is `AlgebraicGeometry.smallEtaleQuasiCoherentCohomologyIsoAtObject`: for an
**arbitrary** object `Z` of the small étale site of `S`, with underlying scheme `Z.left` and
étale structure morphism `Z.hom : Z.left ⟶ S`,

  `H^p(Z.left, Z.hom^* F) ≅ H^p(Z, Fᵃ)`.

## The proof: the collapse of Tag 03P2, run over the object instead of over `S`

The remark says the *proof* of Tag 03P2 gives this, and that is literally what is carried out.
The proof of Tag 03P2 in the case `𝒞 = (Sch/S)_τ`
(`AlgebraicGeometry.bigOverQuasiCoherentCohomologyIso`) is the Leray collapse
`Stacks.Cohomology.BiggerSite.sheafCohomologyPushforwardIso` along
`ε : (Sch/S)_τ ⟶ S_Zar`, whose functor is `Stacks.Adequate.opensBelowToOver`.  Here the same
collapse is run along

`AlgebraicGeometry.opensBelowToOverAlong`, the composite
`Y_Zar ⟶ (Sch/Y)_τ ⟶ (Sch/S)_τ` of the small Zariski site of `Y` inside the big site localized
at `Y` with `CategoryTheory.Over.map` along `f : Y ⟶ S`,

which sends the whole of `Y` to the object `f` of the site over `S` rather than to a final
object.  Its three inputs are the three inputs of Tag 03P2, re-read along that functor:

* **continuity.**  The topology of a localized big site is the localization of the topology of
  the big site (`AlgebraicGeometry.overTopology_eq_siteTopology_over`), so `Over.map` between
  two localizations of one site is continuous; composing with
  `AlgebraicGeometry.isContinuous_opensBelowToOver` gives
  `AlgebraicGeometry.isContinuous_opensBelowToOverAlong`.
* **vanishing of the higher direct images.**  An affine open of `Y` is an affine object of the
  big site over `S` — its total space is the open subscheme itself, which is what
  `AlgebraicGeometry.overAffineObjects` asks about, so the membership is
  `AlgebraicGeometry.IsAffineOpen` unfolded, exactly as for `opensBelowToOver`.  The covering
  families and the affine acyclicity are then shared verbatim with Tag 03P2:
  `AlgebraicGeometry.affineOpensPresieve`, `AlgebraicGeometry.generate_affineOpensPresieve_mem`
  and `AlgebraicGeometry.isZero_sheafCohomology_succ_overAffine`.
* **the degree-zero input.**  What the collapse compares against is the direct image of `Fᵃ`,
  and `AlgebraicGeometry.opensBelowToOverAlongSectionsIso` identifies it with the abelian sheaf
  underlying `f^*F`: the restriction along `Over.map f` of the presheaf of [Stacks, Tag 03DS] of
  `(S, F)` is the presheaf of Tag 03DS of `(Y, f^*F)`
  (`Stacks.Sites.quasiCoherentPresheafBaseChangeIso`), and the remaining restriction to the
  opens of `Y` is `AlgebraicGeometry.bigOverSectionsUnitIso` over `Y`.

The case `𝒞 = S_étale` is the same proof over the same three inputs, run along

`AlgebraicGeometry.opensToEtaleAlong`, the composite `Y_Zar ⟶ Y_étale ⟶ S_étale` of
`AlgebraicGeometry.opensToEtale` with `AlgebraicGeometry.Scheme.Etale.smallEtaleCompose` along an
**étale** `f : Y ⟶ S`,

which sends an open `V` of `Y` to the object `V ⟶ Y ⟶ S` of `S_étale` — étale because an open
immersion is étale and étale morphisms compose — and the whole of `Y` to the object `f` itself
(`AlgebraicGeometry.smallEtaleObjAtTopIso`).  Its three inputs:

* **continuity.**  Composition with an étale morphism is a continuous functor of small étale
  sites (`AlgebraicGeometry.Scheme.Etale.smallEtaleCompose_isContinuous`); composing with
  `AlgebraicGeometry.opensToEtale_isContinuous` gives
  `AlgebraicGeometry.isContinuous_opensToEtaleAlong`.
* **vanishing of the higher direct images.**  An affine open of `Y`, read along `f`, is an
  affine object of `S_étale`: its total space is the open subscheme itself, which is what
  `AlgebraicGeometry.smallEtaleAffineObjects` asks about, so the membership is
  `AlgebraicGeometry.IsAffineOpen` unfolded.  The covering families and the affine acyclicity
  are then shared verbatim with Tag 03P2: `AlgebraicGeometry.affineOpensPresieve`,
  `AlgebraicGeometry.generate_affineOpensPresieve_mem` and
  `AlgebraicGeometry.isZero_sheafCohomology_succ_smallEtaleAffine`.
* **the degree-zero input.**  `AlgebraicGeometry.opensToEtaleAlongSectionsIso`, by the same two
  steps as in the big case: `Stacks.Sites.quasiCoherentPresheafBaseChangeIso` for the presheaf of
  [Stacks, Tag 03DS], and then `AlgebraicGeometry.smallEtaleSectionsUnitIso` over `Y`.  The two
  functors into the schemes over `S` — `smallEtaleCompose f` followed by
  `AlgebraicGeometry.Scheme.Etale.forget` over `S`, and `Scheme.Etale.forget` over `Y` followed
  by `CategoryTheory.Over.map f` — are the same functor, so no transport between them appears.

No sheaf condition is assumed anywhere: `AlgebraicGeometry.bigOverAssociatedSheaf` and
`AlgebraicGeometry.smallEtaleAssociatedSheaf` are sheaves already, Tag 03OG having been proved
in the library.  No form of Tag 03P2 is assumed either; the second assertion is proved from the
same ingredients as Tag 03P2 rather than from Tag 03P2 itself, which is why it needs no
identification of the localization of `(Sch/S)_τ` at `f` with `(Sch/Y)_τ`, and no identification
of the localization of `S_étale` at an object with the small étale site of that object.

## Main definitions

* `AlgebraicGeometry.schemeBelowHom`: a morphism of schemes as a morphism of the size-bounded
  schemes of a big site.
* `AlgebraicGeometry.opensBelowToOverAlong`: the small Zariski site of `Y` inside a localized
  big `τ`-site of `S`, along a morphism `f : Y ⟶ S`.
* `AlgebraicGeometry.opensBelowToOverAlongSectionsIso`: `ℱ_{f^*F} ≅ ε_* Fᵃ` along that functor.
* `AlgebraicGeometry.objAtTopIso`: the whole of `Y` goes to the object `f` of the site over `S`.
* `AlgebraicGeometry.bigOverQuasiCoherentCohomologyIsoAlong`: the comparison over an arbitrary
  open of `Y`.
* `AlgebraicGeometry.opensToEtaleAlong`: the small Zariski site of `Y` inside the small étale
  site of `S`, along an étale `f : Y ⟶ S`.
* `AlgebraicGeometry.opensToEtaleAlongSectionsIso`: `ℱ_{f^*F} ≅ ε_* Fᵃ` along that functor.
* `AlgebraicGeometry.smallEtaleObjAtTopIso`: the whole of `Y` goes to the object `f` of
  `S_étale`.
* `AlgebraicGeometry.smallEtaleQuasiCoherentCohomologyIsoAlong`: the small étale comparison over
  an arbitrary open of `Y`.

## Main results

* `AlgebraicGeometry.isContinuous_opensBelowToOverAlong`,
  `AlgebraicGeometry.isZero_rightDerived_pushforward_opensBelowToOverAlong`: the two inputs of
  the collapse.
* `AlgebraicGeometry.isContinuous_opensToEtaleAlong`,
  `AlgebraicGeometry.isZero_rightDerived_pushforward_opensToEtaleAlong`: the same two inputs on
  the small étale site.
* `AlgebraicGeometry.bigOverAssociatedSheafGlobalCohomologyIso` and
  `AlgebraicGeometry.smallEtaleAssociatedSheafGlobalCohomologyIso`: **Tag 03P3, first
  assertion**, one declaration per case of Tag 03P2.
* `AlgebraicGeometry.bigOverQuasiCoherentCohomologyIsoAtObject` and
  `AlgebraicGeometry.smallEtaleQuasiCoherentCohomologyIsoAtObject`: **Tag 03P3, second
  assertion**, one declaration per case of Tag 03P2.

## Implementation notes

Cohomology is Mathlib's `Ext`-based `CategoryTheory.Sheaf.H'` over an object of a site and
`CategoryTheory.Sheaf.H` globally; the Zariski side is `Sheaf.H'` over `⊤` on the site of opens,
which is the spelling used throughout this repository for the cohomology of a module on a
scheme.  The two sides of the second assertion are not definitionally equal: the left-hand side
is an `Ext`-group in abelian sheaves on `Y.Opens`, the right-hand side an `Ext`-group in abelian
sheaves on the localized big site, respectively on the small étale site of `S`.

The local instances are the ones the two branches of Tag 03P2 supply by name, for the
reasons recorded there: the `Ext` universe and enough injectives on each side, preservation of
injectives by `ε_*`, and — on the small étale site only — the raised priority of
`CategoryTheory.IsGrothendieckAbelian.hasExt`, without which both small étale assertions would
be stated at `Ext` universe `u + 1` and not at the universe
`AlgebraicGeometry.smallEtaleQuasiCoherentGlobalCohomologyIso` is stated at.  All of them are
spelled fully qualified.

`AlgebraicGeometry.opensToEtaleAlong` is continuous as a composite and not by the route
`AlgebraicGeometry.opensToEtale` itself takes.  That route goes through
`AlgebraicGeometry.representablyFlat_opensToEtale`, which rests on
`AlgebraicGeometry.subsingleton_hom_opensToEtale`: a morphism of `S_étale` into an *open
subscheme* of `S` is unique, the structure morphism of an open subscheme being a monomorphism.
Along a general étale `f` the target object is `V ⟶ Y ⟶ S`, whose structure morphism need not be
a monomorphism, and uniqueness fails; the composite's continuity is taken from
`AlgebraicGeometry.Scheme.Etale.smallEtaleCompose_isContinuous` instead, which is proved in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.Basic` by the slice-category
argument rather than by flatness, for exactly this reason.

Preservation of injectives by `ε_*` along the composite needs the fibre products and equalizers
of `Y.Opens` to be preserved by it.  For `AlgebraicGeometry.opensToEtale` that is
`AlgebraicGeometry.opensToEtale_preservesLimitsOfShape_walkingCospan` and
`AlgebraicGeometry.opensToEtale_preservesLimitsOfShape_walkingParallelPair`; the remaining
factor is `AlgebraicGeometry.smallEtaleCompose_preservesLimitsOfShape_walkingCospan` and
`AlgebraicGeometry.smallEtaleCompose_preservesLimitsOfShape_walkingParallelPair` below, both of
which come from `AlgebraicGeometry.Scheme.Etale.forget` reflecting limits and the equality of
functors recorded there.  They are about `smallEtaleCompose` alone and could move next to it.

## References

* [Stacks Project, Tag 03P3](https://stacks.math.columbia.edu/tag/03P3)
* [Stacks Project, Tag 03P2](https://stacks.math.columbia.edu/tag/03P2)
* [Stacks Project, Tag 03OG](https://stacks.math.columbia.edu/tag/03OG)
* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Adequate
open Stacks.Cohomology.HigherDirectImageOnACover
open scoped AlgebraicGeometry

universe u

-- A localized big site is essentially small at the universe of its morphisms, so these two
-- supply its `Ext` universe and enough injectives.  They are not global instances, and
-- `CategoryTheory.Sheaf.H'` is defined through `Ext`, so without them the *statements* below do
-- not even elaborate.
attribute [local instance] Stacks.Cohomology.FreeYonedaUnivLE.enoughInjectives_essentiallySmallSite
  Stacks.Cohomology.FreeYonedaUnivLE.hasExt_essentiallySmallSite

namespace AlgebraicGeometry

variable {S Y : Scheme.{u}} (F : S.Modules) [F.IsQuasicoherent] {τ : CoveringTopology}
  {B : BigSite.{u} τ} (hS : S.size < cutoff τ B) (hY : Y.size < cutoff τ B) (f : Y ⟶ S)

/-! ### The small Zariski site of an object of the site -/

/-- **A morphism of schemes, read as a morphism of the size-bounded schemes of a big site.**
Both source and target being below the cutoff, a morphism of schemes `f : Y ⟶ S` is a morphism
of `AlgebraicGeometry.siteCategory`. -/
public abbrev schemeBelowHom : base B Y hY ⟶ base B S hS := ObjectProperty.homMk f

/-- **The small Zariski site of `Y` inside a localized big `τ`-site of `S`, along `f : Y ⟶ S`.**
An open `V` of `Y` is sent to the object `V ⟶ Y ⟶ S` of the site over `S`; at `f = 𝟙 S` this is
`Stacks.Adequate.opensBelowToOver`, the functor underlying the comparison
`ε : (Sch/S)_τ ⟶ S_Zar` along which [Stacks, Tag 03P2] collapses.

The whole of `Y` is sent to the object `f` itself (`AlgebraicGeometry.objAtTopIso`), which is
what makes the collapse along this functor a statement about an arbitrary object of the site and
not about a final one. -/
public abbrev opensBelowToOverAlong : Y.Opens ⥤ Over (base B S hS) :=
  opensBelowToOver (κ := cutoff τ B) hY ⋙ Over.map (schemeBelowHom hS hY f)

/-- **`Over.map` between two localizations of one big site is continuous.**  The topology of a
localized big site is the localization of the topology of the big site, by
`AlgebraicGeometry.overTopology_eq_siteTopology_over`, and `CategoryTheory.Over.map` between two
slices of one site, each carrying its localized topology, is continuous. -/
public theorem isContinuous_overMapBase :
    (Over.map (schemeBelowHom hS hY f)).IsContinuous (overTopology τ B Y hY)
      (overTopology τ B S hS) := by
  rw [overTopology_eq_siteTopology_over, overTopology_eq_siteTopology_over]
  infer_instance

/-- **`AlgebraicGeometry.opensBelowToOverAlong` is continuous**, being the composite of the
continuous `Stacks.Adequate.opensBelowToOver`
(`AlgebraicGeometry.isContinuous_opensBelowToOver`) with the continuous `Over.map`
(`AlgebraicGeometry.isContinuous_overMapBase`). -/
public instance isContinuous_opensBelowToOverAlong :
    (opensBelowToOverAlong hS hY f).IsContinuous (Opens.grothendieckTopology ↥Y)
      (overTopology τ B S hS) :=
  have := isContinuous_overMapBase hS hY f
  Functor.isContinuous_comp _ _ _ (overTopology τ B Y hY) _

/-- **An affine open of `Y`, read as an object of a localized big `τ`-site of `S` along
`f : Y ⟶ S`, has affine total space.**  The total space of the resulting object is the open
subscheme itself, so this is `AlgebraicGeometry.IsAffineOpen` unfolded, exactly as for
`AlgebraicGeometry.mem_overAffineObjects_opensBelowToOver`. -/
public theorem mem_overAffineObjects_opensBelowToOverAlong {V : Y.Opens} (hV : IsAffineOpen V) :
    (opensBelowToOverAlong hS hY f).obj V ∈ overAffineObjects τ B S hS := hV

/-- **The higher direct images of `Fᵃ` along `AlgebraicGeometry.opensBelowToOverAlong`
vanish.**  This is the hypothesis of the Leray collapse of [Stacks, Tag 03P2], read along the
functor that lands at the object `f` of the site rather than at a final object.

The affine opens below an open of `Y` generate a covering sieve of it, each of them is an affine
object of the big site over `S` by
`AlgebraicGeometry.mem_overAffineObjects_opensBelowToOverAlong`, and the higher cohomology of
`Fᵃ` there vanishes by `AlgebraicGeometry.isZero_sheafCohomology_succ_overAffine`. -/
public theorem isZero_rightDerived_pushforward_opensBelowToOverAlong (p : ℕ) (hp : 0 < p) :
    IsZero ((((opensBelowToOverAlong hS hY f).sheafPushforwardContinuous AddCommGrpCat.{u}
        (Opens.grothendieckTopology ↥Y) (overTopology τ B S hS)).rightDerived p).obj
      (bigOverAssociatedSheaf S F τ B hS)) := by
  refine isZero_rightDerived_pushforward_of_presieve (opensBelowToOverAlong hS hY f) p _
    (fun V ↦ ?_)
  refine ⟨affineOpensPresieve Y V, generate_affineOpensPresieve_mem Y V, fun W g hg ↦ ?_⟩
  exact (isZero_sheafCohomology_succ_overAffine S F τ B hS
      ((opensBelowToOverAlong hS hY f).obj W)
      (mem_overAffineObjects_opensBelowToOverAlong hS hY f hg) p hp).of_iso
    (Stacks.Cohomology.FreeYonedaUnivLE.sheafCohomologyIsoRightDerivedSections
      (overTopology τ B S hS) _ p ((opensBelowToOverAlong hS hY f).obj W)).symm

/-- **`ℱ_{f^*F} ≅ ε_* Fᵃ` along `AlgebraicGeometry.opensBelowToOverAlong`**, the degree-zero
input of [Stacks, Tag 03P2] read over the object `f` of the site.  The abelian sheaf on the
Zariski site of `Y` underlying the quasi-coherent module `f^*F` agrees with the direct image of
`Fᵃ` along the functor that sends an open `V` of `Y` to the object `V ⟶ Y ⟶ S`.

Two steps.  Restricting the presheaf of [Stacks, Tag 03DS] of `(S, F)` along
`CategoryTheory.Over.map f` gives the presheaf of Tag 03DS of `(Y, f^*F)`, by
`Stacks.Sites.quasiCoherentPresheafBaseChangeIso`; the remaining restriction to the opens of `Y`
is `AlgebraicGeometry.bigOverSectionsUnitIso` over `Y`.  The two functors into the slice of all
schemes over `S` — `Over.map` into the localization at `S` followed by
`AlgebraicGeometry.overToSlice`, and `overToSlice` over `Y` followed by `Over.map f` — are the
same functor, so no transport between them appears. -/
public def opensBelowToOverAlongSectionsIso :
    (SheafOfModules.toSheaf Y.ringCatSheaf).obj ((Scheme.Modules.pullback f).obj F) ≅
      ((opensBelowToOverAlong hS hY f).sheafPushforwardContinuous AddCommGrpCat.{u}
        (Opens.grothendieckTopology ↥Y) (overTopology τ B S hS)).obj
          (bigOverAssociatedSheaf S F τ B hS) :=
  bigOverSectionsUnitIso Y ((Scheme.Modules.pullback f).obj F) τ B hY ≪≫
    (fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology ↥Y) AddCommGrpCat.{u}).preimageIso
      (Functor.isoWhiskerLeft
        ((opensBelowToOver (κ := cutoff τ B) hY).op ⋙ (overToSlice τ B Y hY).op)
        (Stacks.Sites.quasiCoherentPresheafBaseChangeIso F (Over.mk f)).symm)

/-- **The whole of `Y` goes to the object `f : Y ⟶ S` of the site.**  The object
`(opensBelowToOverAlong hS hY f).obj ⊤` is `⊤ ⟶ Y ⟶ S`, and `AlgebraicGeometry.Scheme.topIso`
identifies it with `f` itself.  This is what makes
`AlgebraicGeometry.bigOverQuasiCoherentCohomologyIsoAtObject` a statement about an arbitrary
object of the localized big site. -/
public def objAtTopIso :
    (opensBelowToOverAlong hS hY f).obj ⊤ ≅ Over.mk (schemeBelowHom hS hY f) :=
  Over.isoMk ((schemeSizeBelow (cutoff τ B)).isoMk (Scheme.topIso Y))
    (ObjectProperty.hom_ext _ (by
      change (Scheme.topIso Y).hom ≫ f = (⊤ : Y.Opens).ι ≫ f
      simp))

/-! ### Remark 03P3, second assertion -/

-- The Zariski side of the collapse asks for an `Ext` universe and enough injectives in the
-- coefficients themselves; both are available at any coefficient universe dominating the space,
-- but only as theorems.  Preservation of injectives by `ε_*` is likewise a theorem.
attribute [local instance] Stacks.Topology.hasExt_sheafOpens
  Stacks.Topology.enoughInjectives_sheafOpens
  Stacks.Cohomology.BiggerSite.preservesInjectiveObjects_sheafPushforwardContinuous

/-- **The cohomology of `Fᵃ` over an open of `Y` collapses onto Zariski cohomology of `f^*F`.**
For a quasi-coherent module `F` on `S`, a morphism `f : Y ⟶ S` of schemes below the cutoff of a
big `τ`-site, an open `V` of `Y` and a degree `p`,

  `H^p(V, ℱ_{f^*F}) ≅ H^p_τ(V ⟶ Y ⟶ S, Fᵃ)`,

the right-hand side being the cohomology on a localized big `τ`-site of `S` of the associated
module `Fᵃ`, taken over the object `V ⟶ Y ⟶ S`.

This is `Stacks.Cohomology.BiggerSite.sheafCohomologyPushforwardIso` for the continuous functor
`AlgebraicGeometry.opensBelowToOverAlong`, whose hypothesis is discharged by
`AlgebraicGeometry.isZero_rightDerived_pushforward_opensBelowToOverAlong`, read on the Zariski
side through `AlgebraicGeometry.opensBelowToOverAlongSectionsIso`.  At `f = 𝟙 S` it is
`AlgebraicGeometry.bigOverQuasiCoherentCohomologyIso`, the form of [Stacks, Tag 03P2] over an
arbitrary open of `S`. -/
public def bigOverQuasiCoherentCohomologyIsoAlong (p : ℕ) (V : Y.Opens) :
    Sheaf.H' ((SheafOfModules.toSheaf Y.ringCatSheaf).obj
        ((Scheme.Modules.pullback f).obj F)) p V ≅
      Sheaf.H' (bigOverAssociatedSheaf S F τ B hS) p ((opensBelowToOverAlong hS hY f).obj V) :=
  ((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology ↥Y) p).mapIso
      (opensBelowToOverAlongSectionsIso F hS hY f)).app (op V) ≪≫
    Stacks.Cohomology.BiggerSite.sheafCohomologyPushforwardIso
      (Opens.grothendieckTopology ↥Y) (overTopology τ B S hS) (opensBelowToOverAlong hS hY f)
      (bigOverAssociatedSheaf S F τ B hS) V p
      (fun q hq _ ↦ isZero_rightDerived_pushforward_opensBelowToOverAlong F hS hY f q hq)

/-- **[Stacks, Tag 03P3], second assertion, for `𝒞 = (Sch/S)_τ`:** for **any** object `Z` of a
localized big `τ`-site of `S`, with underlying scheme `U = Z.left.obj` and structure morphism
`f = Z.hom.hom : U ⟶ S`,

  `H^p(U, f^*F) ≅ H^p_τ(Z, Fᵃ)`,

the left-hand side being the Zariski cohomology on `U` of the pullback module `f^*F` and the
right-hand side the `τ`-cohomology of the associated module `Fᵃ` over the object `Z` of the
site.

This is `AlgebraicGeometry.bigOverQuasiCoherentCohomologyIsoAlong` at the whole of `U`, whose
image is `Z` by `AlgebraicGeometry.objAtTopIso`.  Nothing is assumed: the source's own proof of
Tag 03P2 is what is run, over `Z` instead of over `S`. -/
@[stacks 03P3 "second assertion, the case 𝒞 = (Sch/S)_τ: H^p(U, f^*F) = H^p_τ(U, Fᵃ) at an \
ARBITRARY object Z of the site, not only at a final one.  τ is a bound variable, so this one \
declaration covers all five of fppf, syntomic, smooth, étale and Zariski.  Nothing is assumed: \
the sheaf condition of Tag 03OG is already carried by bigOverAssociatedSheaf, and Tag 03P2 is \
not invoked either — the collapse its proof runs along opensBelowToOver is run here along \
opensBelowToOverAlong, which lands at the object Z.  The case 𝒞 = S_étale is \
smallEtaleQuasiCoherentCohomologyIsoAtObject"]
public def bigOverQuasiCoherentCohomologyIsoAtObject (p : ℕ) (Z : Over (base B S hS)) :
    Sheaf.H' ((SheafOfModules.toSheaf (Z.left.obj).ringCatSheaf).obj
        ((Scheme.Modules.pullback Z.hom.hom).obj F)) p (⊤ : (Z.left.obj).Opens) ≅
      Sheaf.H' (bigOverAssociatedSheaf S F τ B hS) p Z :=
  bigOverQuasiCoherentCohomologyIsoAlong F hS Z.left.property Z.hom.hom p ⊤ ≪≫
    (((bigOverAssociatedSheaf S F τ B hS).cohomologyPresheaf p).mapIso
      (objAtTopIso hS Z.left.property Z.hom.hom).op).symm

/-! ### Remark 03P3, second assertion, the case `𝒞 = S_étale` -/

section SmallEtale

variable [AlgebraicGeometry.Etale f]

/-- **The small Zariski site of `Y` inside the small étale site of `S`, along an étale
`f : Y ⟶ S`.**  An open `V` of `Y` is sent to the object `V ⟶ Y ⟶ S` of `S_étale`, which is étale
because an open immersion is étale and étale morphisms compose; at `f = 𝟙 S` it is
`AlgebraicGeometry.opensToEtale`, the functor underlying the comparison `ε : S_étale ⟶ S_Zar`
along which [Stacks, Tag 03P2] collapses, up to the canonical isomorphism
`CategoryTheory.MorphismProperty.Over.mapId`.

The whole of `Y` is sent to the object `f` itself
(`AlgebraicGeometry.smallEtaleObjAtTopIso`), which is what makes the collapse along this functor
a statement about an arbitrary object of the small étale site and not about a final one. -/
@[sga "4 VII 4.2.2" "Inclusion functor u*"]
public abbrev opensToEtaleAlong : Y.Opens ⥤ S.Etale :=
  opensToEtale Y ⋙ Scheme.Etale.smallEtaleCompose f

/-- **`AlgebraicGeometry.opensToEtaleAlong` is continuous**, being the composite of the continuous
`AlgebraicGeometry.opensToEtale` (`AlgebraicGeometry.opensToEtale_isContinuous`) with composition
along `f`, which is continuous by
`AlgebraicGeometry.Scheme.Etale.smallEtaleCompose_isContinuous`. -/
public instance isContinuous_opensToEtaleAlong :
    (opensToEtaleAlong f).IsContinuous (Opens.grothendieckTopology ↥Y)
      (Scheme.smallEtaleTopology S) :=
  Functor.isContinuous_comp _ _ _ (Scheme.smallEtaleTopology Y) _

/-- **Composition with an étale morphism preserves fibre products of small étale sites.**  Fibre
products are connected limits, so they are computed on underlying schemes on both sides:
`AlgebraicGeometry.Scheme.Etale.smallEtaleCompose f ⋙ Scheme.Etale.forget S` is
`Scheme.Etale.forget Y ⋙ CategoryTheory.Over.map f` by definition, that composite preserves
them, and `Scheme.Etale.forget S` is fully faithful and hence reflects them. -/
public instance smallEtaleCompose_preservesLimitsOfShape_walkingCospan :
    PreservesLimitsOfShape WalkingCospan (Scheme.Etale.smallEtaleCompose f) :=
  have : PreservesLimitsOfShape WalkingCospan
      (Scheme.Etale.smallEtaleCompose f ⋙ Scheme.Etale.forget S) :=
    inferInstanceAs (PreservesLimitsOfShape WalkingCospan
      (Scheme.Etale.forget Y ⋙ Over.map f))
  preservesLimitsOfShape_of_reflects_of_preserves (Scheme.Etale.smallEtaleCompose f)
    (Scheme.Etale.forget S)

/-- **Composition with an étale morphism preserves equalizers of small étale sites**, for the
reason of `AlgebraicGeometry.smallEtaleCompose_preservesLimitsOfShape_walkingCospan`: a parallel
pair is a connected diagram too. -/
public instance smallEtaleCompose_preservesLimitsOfShape_walkingParallelPair :
    PreservesLimitsOfShape WalkingParallelPair (Scheme.Etale.smallEtaleCompose f) :=
  have : PreservesLimitsOfShape WalkingParallelPair
      (Scheme.Etale.smallEtaleCompose f ⋙ Scheme.Etale.forget S) :=
    inferInstanceAs (PreservesLimitsOfShape WalkingParallelPair
      (Scheme.Etale.forget Y ⋙ Over.map f))
  preservesLimitsOfShape_of_reflects_of_preserves (Scheme.Etale.smallEtaleCompose f)
    (Scheme.Etale.forget S)

/-- **An affine open of `Y`, read as an object of the small étale site of `S` along an étale
`f : Y ⟶ S`, has affine total space.**  The total space of the resulting object is the open
subscheme itself, so this is `AlgebraicGeometry.IsAffineOpen` unfolded, exactly as for
`AlgebraicGeometry.mem_smallEtaleAffineObjects_opensToEtale`. -/
public theorem mem_smallEtaleAffineObjects_opensToEtaleAlong {V : Y.Opens}
    (hV : IsAffineOpen V) : (opensToEtaleAlong f).obj V ∈ smallEtaleAffineObjects S := hV

/-- **The higher direct images of `Fᵃ` along `AlgebraicGeometry.opensToEtaleAlong` vanish.**
This is the hypothesis of the Leray collapse of [Stacks, Tag 03P2] in the case `𝒞 = S_étale`,
read along the functor that lands at the object `f` of the site rather than at a final object.

The affine opens below an open of `Y` generate a covering sieve of it, each of them is an affine
object of the small étale site of `S` by
`AlgebraicGeometry.mem_smallEtaleAffineObjects_opensToEtaleAlong`, and the higher cohomology of
`Fᵃ` there vanishes by `AlgebraicGeometry.isZero_sheafCohomology_succ_smallEtaleAffine`. -/
public theorem isZero_rightDerived_pushforward_opensToEtaleAlong (p : ℕ) (hp : 0 < p) :
    IsZero ((((opensToEtaleAlong f).sheafPushforwardContinuous AddCommGrpCat.{u}
        (Opens.grothendieckTopology ↥Y) (Scheme.smallEtaleTopology S)).rightDerived p).obj
      (smallEtaleAssociatedSheaf S F)) := by
  refine isZero_rightDerived_pushforward_of_presieve (opensToEtaleAlong f) p _ (fun V ↦ ?_)
  refine ⟨affineOpensPresieve Y V, generate_affineOpensPresieve_mem Y V, fun W g hg ↦ ?_⟩
  exact (isZero_sheafCohomology_succ_smallEtaleAffine S F ((opensToEtaleAlong f).obj W)
      (mem_smallEtaleAffineObjects_opensToEtaleAlong f hg) p hp).of_iso
    (Stacks.Cohomology.FreeYonedaUnivLE.sheafCohomologyIsoRightDerivedSections
      (Scheme.smallEtaleTopology S) _ p ((opensToEtaleAlong f).obj W)).symm

/-- **`ℱ_{f^*F} ≅ ε_* Fᵃ` along `AlgebraicGeometry.opensToEtaleAlong`**, the degree-zero input of
[Stacks, Tag 03P2] read over the object `f` of the small étale site.  The abelian sheaf on the
Zariski site of `Y` underlying the quasi-coherent module `f^*F` agrees with the direct image of
`Fᵃ` along the functor that sends an open `V` of `Y` to the object `V ⟶ Y ⟶ S`.

Two steps, as in `AlgebraicGeometry.opensBelowToOverAlongSectionsIso`.  Restricting the presheaf
of [Stacks, Tag 03DS] of `(S, F)` along `CategoryTheory.Over.map f` gives the presheaf of
Tag 03DS of `(Y, f^*F)`, by `Stacks.Sites.quasiCoherentPresheafBaseChangeIso`; the remaining
restriction to the opens of `Y` is `AlgebraicGeometry.smallEtaleSectionsUnitIso` over `Y`.  The
two functors into the schemes over `S` — composition along `f` followed by
`AlgebraicGeometry.Scheme.Etale.forget` over `S`, and `Scheme.Etale.forget` over `Y` followed by
`Over.map f` — are the same functor, so no transport between them appears. -/
public def opensToEtaleAlongSectionsIso :
    (SheafOfModules.toSheaf Y.ringCatSheaf).obj ((Scheme.Modules.pullback f).obj F) ≅
      ((opensToEtaleAlong f).sheafPushforwardContinuous AddCommGrpCat.{u}
        (Opens.grothendieckTopology ↥Y) (Scheme.smallEtaleTopology S)).obj
          (smallEtaleAssociatedSheaf S F) :=
  smallEtaleSectionsUnitIso Y ((Scheme.Modules.pullback f).obj F) ≪≫
    (fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology ↥Y) AddCommGrpCat.{u}).preimageIso
      (Functor.isoWhiskerLeft ((opensToEtale Y).op ⋙ (Scheme.Etale.forget Y).op)
        (Stacks.Sites.quasiCoherentPresheafBaseChangeIso F (Over.mk f)).symm)

/-- **The whole of `Y` goes to the object `f : Y ⟶ S` of the small étale site.**  The object
`(opensToEtaleAlong f).obj ⊤` is `⊤ ⟶ Y ⟶ S`, and `AlgebraicGeometry.Scheme.topIso` identifies it
with `f` itself.  This is what makes
`AlgebraicGeometry.smallEtaleQuasiCoherentCohomologyIsoAtObject` a statement about an arbitrary
object of the small étale site. -/
public def smallEtaleObjAtTopIso : (opensToEtaleAlong f).obj ⊤ ≅ Scheme.Etale.mk f :=
  MorphismProperty.Over.isoMk (Scheme.topIso Y) rfl

-- `CategoryTheory.Sheaf.H'` carries its `Ext` universe as a parameter, and on the small étale
-- site instance search resolves it to `u + 1` rather than to the morphism universe `u`, because
-- `AlgebraicGeometry.hasExt_sheaf_smallEtaleTopology` is declared after
-- `CategoryTheory.IsGrothendieckAbelian.hasExt` and so wins.  The library's form of
-- [Stacks, Tag 03P2] on this site measures at `u`, so the priority has to be flipped here too,
-- exactly as in `AlgebraicGeometry.smallEtaleQuasiCoherentCohomologyIso`.
attribute [local instance 2000] CategoryTheory.IsGrothendieckAbelian.hasExt in
/-- **The cohomology of `Fᵃ` over an open of `Y` collapses onto Zariski cohomology of `f^*F`.**
For a quasi-coherent module `F` on `S`, an **étale** morphism `f : Y ⟶ S`, an open `V` of `Y` and
a degree `p`,

  `H^p(V, ℱ_{f^*F}) ≅ H^p(V ⟶ Y ⟶ S, Fᵃ)`,

the right-hand side being the cohomology on the small étale site of `S` of the associated module
`Fᵃ`, taken over the object `V ⟶ Y ⟶ S`.

This is `Stacks.Cohomology.BiggerSite.sheafCohomologyPushforwardIso` for the continuous functor
`AlgebraicGeometry.opensToEtaleAlong`, whose hypothesis is discharged by
`AlgebraicGeometry.isZero_rightDerived_pushforward_opensToEtaleAlong`, read on the Zariski side
through `AlgebraicGeometry.opensToEtaleAlongSectionsIso`.  It is the same collapse that
`AlgebraicGeometry.smallEtaleQuasiCoherentCohomologyIso` — the form of [Stacks, Tag 03P2] over an
arbitrary open of `S` — runs along `AlgebraicGeometry.opensToEtale`, which is the case
`f = 𝟙 S`. -/
public def smallEtaleQuasiCoherentCohomologyIsoAlong (p : ℕ) (V : Y.Opens) :
    Sheaf.H' ((SheafOfModules.toSheaf Y.ringCatSheaf).obj
        ((Scheme.Modules.pullback f).obj F)) p V ≅
      Sheaf.H' (smallEtaleAssociatedSheaf S F) p ((opensToEtaleAlong f).obj V) :=
  ((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology ↥Y) p).mapIso
      (opensToEtaleAlongSectionsIso F f)).app (op V) ≪≫
    Stacks.Cohomology.BiggerSite.sheafCohomologyPushforwardIso
      (Opens.grothendieckTopology ↥Y) (Scheme.smallEtaleTopology S) (opensToEtaleAlong f)
      (smallEtaleAssociatedSheaf S F) V p
      (fun q hq _ ↦ isZero_rightDerived_pushforward_opensToEtaleAlong F f q hq)

end SmallEtale

attribute [local instance 2000] CategoryTheory.IsGrothendieckAbelian.hasExt in
/-- **[Stacks, Tag 03P3], second assertion, for `𝒞 = S_étale`:** for **any** object `Z` of the
small étale site of `S`, with underlying scheme `U = Z.left` and étale structure morphism
`f = Z.hom : U ⟶ S`,

  `H^p(U, f^*F) ≅ H^p(Z, Fᵃ)`,

the left-hand side being the Zariski cohomology on `U` of the pullback module `f^*F` and the
right-hand side the cohomology of the associated module `Fᵃ` on the small étale site of `S`,
taken over the object `Z` of that site.

This is `AlgebraicGeometry.smallEtaleQuasiCoherentCohomologyIsoAlong` at the whole of `U`, whose
image is `Z` by `AlgebraicGeometry.smallEtaleObjAtTopIso`.  Nothing is assumed: the source's own
proof of Tag 03P2 is what is run, over `Z` instead of over `S`. -/
@[stacks 03P3 "second assertion, the case 𝒞 = S_étale: H^p(U, f^*F) = H^p(U, Fᵃ) at an \
ARBITRARY object Z of the small étale site of S, not only at a final one.  Nothing is assumed: \
the sheaf condition of Tag 03OG is already carried by smallEtaleAssociatedSheaf, and Tag 03P2 is \
not invoked either — the collapse its proof runs along opensToEtale is run here along \
opensToEtaleAlong, the composite of opensToEtale over U with composition along the étale \
structure morphism of Z, which lands at the object Z.  The case 𝒞 = (Sch/S)_τ is \
bigOverQuasiCoherentCohomologyIsoAtObject"]
public def smallEtaleQuasiCoherentCohomologyIsoAtObject (p : ℕ) (Z : S.Etale) :
    Sheaf.H' ((SheafOfModules.toSheaf Z.left.ringCatSheaf).obj
        ((Scheme.Modules.pullback Z.hom).obj F)) p (⊤ : Z.left.Opens) ≅
      Sheaf.H' (smallEtaleAssociatedSheaf S F) p Z :=
  smallEtaleQuasiCoherentCohomologyIsoAlong F Z.hom p ⊤ ≪≫
    (((smallEtaleAssociatedSheaf S F).cohomologyPresheaf p).mapIso
      (smallEtaleObjAtTopIso Z.hom).op).symm

/-! ### Remark 03P3, first assertion -/

/-- **[Stacks, Tag 03P3], first assertion, for `𝒞 = (Sch/S)_τ`:** the scheme `S` is a final
object of a localized big `τ`-site of `S`, so the groups `H^p_τ(S, Fᵃ)` on the right-hand side
of [Stacks, Tag 03P2] are the right derived functors of the global sections functor of the site,
that is Mathlib's global `CategoryTheory.Sheaf.H`.

The object on the left is `(opensBelowToOver hS).obj ⊤`, which is exactly the object
`AlgebraicGeometry.bigOverQuasiCoherentGlobalCohomologyIso` takes its right-hand side over, and
it is final by `AlgebraicGeometry.isTerminal_opensBelowToOver_top`. -/
@[stacks 03P3 "first assertion, the case 𝒞 = (Sch/S)_τ: since S is final in 𝒞 the right-hand \
side of Tag 03P2 is derived global sections.  The object is the very one \
bigOverQuasiCoherentGlobalCohomologyIso lands at, and it is final by \
isTerminal_opensBelowToOver_top; τ is a bound variable, so all five topologies are covered.  \
The case 𝒞 = S_étale is smallEtaleAssociatedSheafGlobalCohomologyIso"]
public def bigOverAssociatedSheafGlobalCohomologyIso (p : ℕ) :
    Sheaf.H' (bigOverAssociatedSheaf S F τ B hS) p
        ((opensBelowToOver (κ := cutoff τ B) hS).obj ⊤) ≅
      AddCommGrpCat.of (Sheaf.H.{u} (bigOverAssociatedSheaf S F τ B hS) p) :=
  Stacks.Cohomology.TerminalCohomology.h'IsoH (overTopology τ B S hS)
    (bigOverAssociatedSheaf S F τ B hS) p _ (isTerminal_opensBelowToOver_top hS)

-- `CategoryTheory.Sheaf.H'` and `CategoryTheory.Sheaf.H` carry their `Ext` universe as a
-- parameter, and on the small étale site instance search resolves it to `u + 1` rather than to
-- the morphism universe `u`, because `AlgebraicGeometry.hasExt_sheaf_smallEtaleTopology` is
-- declared after `CategoryTheory.IsGrothendieckAbelian.hasExt` and so wins.  The library's form of
-- [Stacks, Tag 03P2] on this site measures at `u`, so the priority has to be flipped here too,
-- exactly as in `AlgebraicGeometry.smallEtaleQuasiCoherentCohomologyIso`.
attribute [local instance 2000] CategoryTheory.IsGrothendieckAbelian.hasExt in
/-- **[Stacks, Tag 03P3], first assertion, for `𝒞 = S_étale`:** the scheme `S` is a final object
of its small étale site, so the groups `H^p(S_étale, Fᵃ)` on the right-hand side of
[Stacks, Tag 03P2] are the right derived functors of the global sections functor of the site.

The object on the left is `(opensToEtale S).obj ⊤`, which is exactly the object
`AlgebraicGeometry.smallEtaleQuasiCoherentGlobalCohomologyIso` takes its right-hand side over,
and it is final by `AlgebraicGeometry.isTerminal_opensToEtale_top`. -/
@[stacks 03P3 "first assertion, the case 𝒞 = S_étale: since S is final in S_étale the \
right-hand side of Tag 03P2 is derived global sections.  The object is the very one \
smallEtaleQuasiCoherentGlobalCohomologyIso lands at, and it is final by \
isTerminal_opensToEtale_top.  The case 𝒞 = (Sch/S)_τ is \
bigOverAssociatedSheafGlobalCohomologyIso"]
public def smallEtaleAssociatedSheafGlobalCohomologyIso (S : Scheme.{u}) (F : S.Modules)
    [F.IsQuasicoherent] (p : ℕ) :
    Sheaf.H' (smallEtaleAssociatedSheaf S F) p ((opensToEtale S).obj ⊤) ≅
      AddCommGrpCat.of (Sheaf.H.{u} (smallEtaleAssociatedSheaf S F) p) :=
  Stacks.Cohomology.TerminalCohomology.h'IsoH (Scheme.smallEtaleTopology S)
    (smallEtaleAssociatedSheaf S F) p _ (isTerminal_opensToEtale_top S)

end AlgebraicGeometry

end
