module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseOpenCoverQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseRingedSite
public import StacksFrontier.AlgebraicGeometry.Descent.LocallyRingedBigSites
public import StacksFrontier.AlgebraicGeometry.Picard.BigSitesFirstCohomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EssentiallySmallInternalHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.PicardGroupOfARingedSiteGeneral
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseRingedSiteHomGeneral

/-!
# First cohomology of the units on the five big sites of a scheme, at one stroke

Let `S` be a scheme of a big fppf site `B`.  The five topologies of
`AlgebraicGeometry.SiteKind` all live on the *same* category `(Sch/S)` of schemes over `S`
through `AlgebraicGeometry.BigFppfOver.baseOverTopology`, and the structure sheaf
`T/S ↦ Γ(T, 𝒪_T)` is a sheaf for every one of them.  So the five big `τ`-sites of `S` are five
ringed sites with one underlying category, `AlgebraicGeometry.BigFppfOver.baseRingedSite`, and
one statement quantified over `τ` carries all five.

Each of them is locally ringed, and feeding that to the identification of the first cohomology
of the units with the Picard group of a locally ringed site (Tag 040E) gives

`H¹_τ(S, 𝐆_m) = Pic(𝒪_τ)`,

normalized on every invertible `𝒪_τ`-module by its torsor of local generators, for every
`τ ∈ {Zariski, étale, smooth, syntomic, fppf}`.

## Main definitions

* `AlgebraicGeometry.BigFppfOver.baseRingedSite`: the big `τ`-site of `S` with the sheaf of
  global functions as its structure sheaf, read as a ringed site.
* `Stacks.Picard.BaseSites.baseH1UnitsAddEquivPicardGroup`: **the identification
  `H¹_τ(S, 𝐆_m) = Pic(𝒪_τ)`**, at every `τ`.

## Main results

* `AlgebraicGeometry.BigFppfOver.baseOver_openCoverData`: every open cover of the scheme
  underlying an object of `(Sch/S)` is refined by a covering family of the big `τ`-site, for
  every `τ`.
* `AlgebraicGeometry.baseRingedSite_isLocallyRinged`: **the big `τ`-site of `S` is locally
  ringed**, at every `τ`.
* `Stacks.Picard.BaseSites.baseH1UnitsAddEquivPicardGroup_symm_classOf`: the identification
  sends the class of an invertible module to the cohomology class of its torsor of generators,
  which fixes it rather than only asserting that one exists.

## Implementation notes

`AlgebraicGeometry.BigFppfOver.baseRingedSite B S hS .fppf` is
`AlgebraicGeometry.bigFppfOverRingedSite B S hS` on the nose, which
`AlgebraicGeometry.BigFppfOver.baseRingedSite_fppf` records: the two topologies are the same
term, the two structure presheaves are the same functor, and the two sheaf conditions are
proofs of one proposition.  The four coarser topologies have no counterpart among
`AlgebraicGeometry.bigZariskiOverRingedSite` and its three siblings, which are built over a big
*Zariski*, *étale*, *smooth* or *syntomic* site — a different structure, with its own size
cutoff and its own chosen covering families — rather than over a big fppf site.  That is why
local ringedness is proved here again rather than quoted from
`StacksFrontier/AlgebraicGeometry/Descent/LocallyRingedBigSites.lean`: the statements there are
about the four other ambient sites and do not apply.

The open-cover refinement is the one of
`AlgebraicGeometry.bigFppfOver_zariski_openCoverData` — an open cover of the scheme underlying
an object, read as a family of open immersions — fed to
`AlgebraicGeometry.BigFppfOver.sieve₀_mem_baseTopology_of_isOpenImmersion`, which is exactly
the statement that such a family covers for each of the five topologies.

`HasExt` is an instance binder rather than an instance, as in
`Stacks.Picard.BigSites`: the universe in which the `Ext`-groups live is a parameter of
`HasExt` and is not determined by the site.  At the universe of the morphisms of the sheaf
category it is a theorem,
`AlgebraicGeometry.BigFppfOver.hasExt_sheaf_baseOverTopology`.

## References

* [Stacks Project, Tag 040E](https://stacks.math.columbia.edu/tag/040E)
* [Stacks Project, Tag 04EU](https://stacks.math.columbia.edu/tag/04EU)
* [Stacks Project, Tag 0GZV](https://stacks.math.columbia.edu/tag/0GZV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe t u

namespace AlgebraicGeometry

namespace BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The ringed site of the big fppf site of `S` built here is the one of
`AlgebraicGeometry.bigFppfOverRingedSite`: same category, same topology, same structure
presheaf, and the two sheaf conditions are proofs of one proposition. -/
public theorem baseRingedSite_fppf :
    baseRingedSite B S hS .fppf = bigFppfOverRingedSite B S hS := rfl

/-- The sheaf of rings of the big `τ`-ringed site over `S` is the coefficient sheaf for modules
there: a sheaf of modules on `baseRingedSite B S hS τ` *is* one over
`AlgebraicGeometry.FibredSite.baseRingStructureSheaf`, with no comparison. -/
public theorem baseRingedSite_ringSheaf (τ : SiteKind) :
    (Stacks.SheafOfModules.Tensor.ringSheaf (baseRingedSite B S hS τ).O) =
      FibredSite.baseRingStructureSheaf B S hS τ := rfl

/-- **Every open cover of the scheme underlying an object of `(Sch/S)` is refined by a covering
family of the big `τ`-site**, for every one of the five topologies.

The family is the one cut out by the open cover itself, whose members are open immersions, and
`AlgebraicGeometry.BigFppfOver.sieve₀_mem_baseTopology_of_isOpenImmersion` says that a jointly
surjective family of open immersions covers for each of the five covering predicates. -/
public theorem baseOver_openCoverData (τ : SiteKind) :
    ∀ {T : BigFppfOver B S hS}
      (U : (BigFppfOver.toScheme B S hS).obj T →
        ((BigFppfOver.toScheme B S hS).obj T).Opens),
      IsOpenCover U →
      ∃ (I : Type (u + 1)) (W : I → BigFppfOver B S hS) (a : ∀ i, W i ⟶ T)
        (r : I → (BigFppfOver.toScheme B S hS).obj T),
        Sieve.ofArrows W a ∈ baseOverTopology B S hS τ T ∧
          ∀ i y, (BigFppfOver.toScheme B S hS).map (a i) y ∈ U (r i) := by
  intro T U hU
  let F := BigFppfOver.toScheme B S hS
  let X := F.obj T
  let U' : ULift.{u + 1, u} X → X.Opens := fun i => U i.down
  have hU' : IsOpenCover U' := by
    rw [IsOpenCover] at hU ⊢
    simpa [U'] using hU
  let O : X.OpenCover.{u + 1} := X.openCoverOfIsOpenCover U' hU'
  let V : O.I₀ → B.Schemes := fun i =>
    ⟨O.X i, Scheme.size_lt_of_isOpenImmersion (O.f i) T.left.2⟩
  let f : ∀ i, V i ⟶ T.left := fun i => ⟨O.f i⟩
  let E : PreZeroHypercover.{u + 1} T.left := ⟨O.I₀, V, f⟩
  let W : O.I₀ → BigFppfOver B S hS := fun i => Over.mk (f i ≫ T.hom)
  let a : ∀ i, W i ⟶ T := fun i => Over.homMk (f i) (by simp [W])
  have hsurj : ∀ x : ↥(B.inclusion.obj T.left), ∃ i, x ∈ Set.range ⇑(B.inclusion.map (E.f i)) :=
    ((Scheme.presieve₀_mem_precoverage_iff O.toPreZeroHypercover).1 O.mem₀).1
  have himm : ∀ i, IsOpenImmersion (B.inclusion.map (E.f i)) := fun i =>
    inferInstanceAs (IsOpenImmersion (O.f i))
  have hcover : Sieve.ofArrows W a ∈ baseOverTopology B S hS τ T := by
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    show Sieve.ofArrows V f ∈ B.baseTopology τ T.left
    exact sieve₀_mem_baseTopology_of_isOpenImmersion B τ E hsurj himm
  refine ⟨O.I₀, W, a, fun i => i.down, hcover, fun i y => ?_⟩
  show y.1 ∈ U' i
  simpa [U'] using y.2

end BigFppfOver

/-- **The big `τ`-site of a scheme is locally ringed**, for every one of the five topologies.

This is `AlgebraicGeometry.RingedSite.isLocallyRinged_globalFunctions`, Stacks 04EU for a site
of schemes carrying global functions, fed the open-cover refinement
`AlgebraicGeometry.BigFppfOver.baseOver_openCoverData`. -/
public theorem baseRingedSite_isLocallyRinged (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (τ : SiteKind) :
    RingedSite.IsLocallyRinged (BigFppfOver.baseRingedSite B S hS τ) :=
  RingedSite.isLocallyRinged_globalFunctions _ (BigFppfOver.toScheme B S hS)
    (BigFppfOver.baseRingedSite B S hS τ).O.property
    (BigFppfOver.baseOver_openCoverData B S hS τ)

end AlgebraicGeometry

namespace Stacks.Picard.BaseSites

open _root_.AlgebraicGeometry

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (τ : SiteKind)

/-- The big `τ`-site over `S` is essentially small in the universe of the schemes. -/
public instance baseEssentiallySmall :
    EssentiallySmall.{u} (BigFppfOver.baseRingedSite B S hS τ).C :=
  Stacks.essentiallySmall_over.{u} _

/-- Abelian presheaves sheafify on every slice of the big `τ`-ringed site over `S`. -/
public instance baseHasSheafifyOver (V : (BigFppfOver.baseRingedSite B S hS τ).C) :
    HasSheafify ((BigFppfOver.baseRingedSite B S hS τ).J.over V) AddCommGrpCat.{u} :=
  Stacks.Picard.BigSites.hasSheafify_over_addCommGrp _ V

/-- Sheafification on every slice of the big `τ`-ringed site over `S` inverts exactly the
locally bijective morphisms of abelian presheaves. -/
public instance baseWEqualsLocallyBijectiveOver (V : (BigFppfOver.baseRingedSite B S hS τ).C) :
    ((BigFppfOver.baseRingedSite B S hS τ).J.over V).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  Stacks.Picard.BigSites.wEqualsLocallyBijective_over_addCommGrp _ V

/-- The abelian group structure on the Picard group of the big `τ`-ringed site, named because
instance search does not find it through the universe constraints of a ringed site. -/
public instance basePicardGroupAddCommGroup :
    AddCommGroup (Stacks.SheafOfModules.Picard.PicardGroup
      (BigFppfOver.baseRingedSite B S hS τ).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (BigFppfOver.baseRingedSite B S hS τ).O).2) :=
  Stacks.SheafOfModules.Picard.instAddCommGroupPicardGroup
    (BigFppfOver.baseRingedSite B S hS τ).O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf (BigFppfOver.baseRingedSite B S hS τ).O).2

variable [HasExt.{t} (Sheaf (BigFppfOver.baseRingedSite B S hS τ).J AddCommGrpCat.{u})]

/-- **Tag 040E on the big `τ`-site of a scheme, at every one of the five topologies.** For a
scheme `S` in a big fppf site containing it there is a canonical isomorphism of abelian groups
`H¹_τ(S, 𝐆_m) = Pic(𝒪_τ)` on the big `τ`-site over `S`. -/
public def baseH1UnitsAddEquivPicardGroup :
    Sheaf.H (Stacks.Cohomology.Torsors.Generators.unitsAddSheaf
        (BigFppfOver.baseRingedSite B S hS τ)) 1 ≃+
      Stacks.SheafOfModules.Picard.PicardGroup (BigFppfOver.baseRingedSite B S hS τ).O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (BigFppfOver.baseRingedSite B S hS τ).O).2 :=
  Stacks.Cohomology.Torsors.Generators.h1UnitsAddEquivPicardGroup'
    (BigFppfOver.baseRingedSite B S hS τ) (baseRingedSite_isLocallyRinged B S hS τ)

/-- The identification on the big `τ`-site is the canonical one: its inverse sends the class of
an invertible module to the first cohomology class of its torsor of local generators. -/
public theorem baseH1UnitsAddEquivPicardGroup_symm_classOf
    (L : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (BigFppfOver.baseRingedSite B S hS τ).O))
    (hL : Stacks.SheafOfModules.IsInvertible (BigFppfOver.baseRingedSite B S hS τ).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (BigFppfOver.baseRingedSite B S hS τ).O).2 L) :
    (baseH1UnitsAddEquivPicardGroup B S hS τ).symm
        (Stacks.SheafOfModules.Picard.classOf (BigFppfOver.baseRingedSite B S hS τ).O.obj
          (Stacks.SheafOfModules.Tensor.ringSheaf (BigFppfOver.baseRingedSite B S hS τ).O).2 L hL) =
      Stacks.Cohomology.Torsors.torsorIsoClassesEquivH1
        (Stacks.Cohomology.Torsors.Generators.unitsAddSheaf
          (BigFppfOver.baseRingedSite B S hS τ))
        (Quotient.mk (Stacks.Cohomology.Torsors.torsorSetoid
            (Stacks.Cohomology.Torsors.Generators.unitsAddSheaf
              (BigFppfOver.baseRingedSite B S hS τ)))
          (Stacks.Cohomology.Torsors.Generators.generatorTorsor'
            (BigFppfOver.baseRingedSite B S hS τ)
            (baseRingedSite_isLocallyRinged B S hS τ) L hL).torsor) :=
  Stacks.Cohomology.Torsors.Generators.h1UnitsAddEquivPicardGroup_symm_classOf'
    (BigFppfOver.baseRingedSite B S hS τ) (baseRingedSite_isLocallyRinged B S hS τ) L hL

end Stacks.Picard.BaseSites

end
