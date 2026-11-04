module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.CohomologyAtTheTerminalObject
public import StacksFrontier.Topology.Sheaves.Cohomology.Locality.CohomologyVanishesLocally
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.CohomologyPresheafComparison

/-!
# Cohomology over the whole space of a module sheaf is global abelian sheaf cohomology

For a sheaf of modules `F` on a ringed space, `Hgroup R ⊤ n F` — the `n`-th right derived functor
of sections over `⊤`, computed in `Mod(𝒪_X)` — is Mathlib's `Ext`-theoretic sheaf cohomology
`Sheaf.H` of the underlying abelian sheaf of `F`.

The isomorphism is a composite of two comparisons:
`Stacks.Cohomology.ModuleComparison.rightDerivedSectionsIsoCohomologyPresheaf`, which identifies
derived sections over an object of the site with the value of Mathlib's cohomology presheaf, and
`Stacks.Cohomology.TerminalCohomology.h'IsoH`, which identifies that value at a terminal object
with global sheaf cohomology. The terminal object of the site of opens is `⊤`.

## Main definitions

* `Stacks.Cohomology.ModuleComparison.hgroupTopIsoSheafH` and `hgroupTopAddEquivSheafH`: the
  composite comparison, as an isomorphism in `AddCommGrpCat` and as an additive equivalence.

## Main results

* `Stacks.Cohomology.ModuleComparison.isZero_hgroupTop_iff_subsingleton_sheafH`: the two models
  vanish together.
* `Stacks.Cohomology.ModuleComparison.eq_zero_sheafH_of_isZero_hgroupTop`: every global
  cohomology class of the underlying abelian sheaf is zero as soon as `Hgroup R ⊤ n F` is a zero
  object. This is the direction consumed by the local cohomology vanishing results.

## Implementation notes

The second factor of the comparison is a choice, so no compatibility in degree zero with the
canonical map to the right derived functor is claimed; the intended use is the transport of
vanishing.

`Sheaf.H` carries a universe for its `Ext`-groups that is independent of the universe of the
site, and the comparison exists only when the two agree; both are pinned to `u` here, as
everywhere in this development.

## References

* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry

universe u

namespace Stacks.Cohomology.ModuleComparison

section RingedSpace

variable {X : Type u} [TopologicalSpace X]
  (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [EnoughInjectives (SheafOfModules.{u} R)]
  [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
  [HasInjectiveResolutions (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

/-- **Cohomology over `⊤` of a module sheaf is global abelian sheaf cohomology.** The degree-`n`
cohomology of `F` over the whole space, computed by deriving sections in `Mod(𝒪_X)`, is the
degree-`n` sheaf cohomology of the underlying abelian sheaf of `F`. -/
def hgroupTopIsoSheafH (n : ℕ) (F : SheafOfModules.{u} R) :
    Hgroup R ⊤ n F ≅
      AddCommGrpCat.of (Sheaf.H.{u} ((SheafOfModules.toSheaf.{u} R).obj F) n) :=
  rightDerivedSectionsIsoCohomologyPresheaf (Opens.grothendieckTopology X) R (⊤ : Opens X) n F ≪≫
    TerminalCohomology.h'IsoH (Opens.grothendieckTopology X)
      ((SheafOfModules.toSheaf.{u} R).obj F) n (⊤ : Opens X) TerminalCohomology.topIsTerminal

/-- The comparison `hgroupTopIsoSheafH`, read as an additive equivalence of the underlying
groups. -/
def hgroupTopAddEquivSheafH (n : ℕ) (F : SheafOfModules.{u} R) :
    Hgroup R ⊤ n F ≃+ Sheaf.H.{u} ((SheafOfModules.toSheaf.{u} R).obj F) n :=
  (hgroupTopIsoSheafH R n F).addCommGroupIsoToAddEquiv

/-- **The two models of global cohomology vanish together.** -/
theorem isZero_hgroupTop_iff_subsingleton_sheafH (n : ℕ) (F : SheafOfModules.{u} R) :
    IsZero (Hgroup R ⊤ n F) ↔
      Subsingleton (Sheaf.H.{u} ((SheafOfModules.toSheaf.{u} R).obj F) n) := by
  rw [AddCommGrpCat.isZero_iff_subsingleton]
  exact ⟨fun _ => (hgroupTopAddEquivSheafH R n F).toEquiv.symm.subsingleton,
    fun _ => (hgroupTopAddEquivSheafH R n F).toEquiv.subsingleton⟩

/-- **Vanishing of cohomology over `⊤` in `Mod(𝒪_X)` kills every global cohomology class of the
underlying abelian sheaf.** -/
theorem eq_zero_sheafH_of_isZero_hgroupTop (n : ℕ) (F : SheafOfModules.{u} R)
    (h : IsZero (Hgroup R ⊤ n F))
    (x : Sheaf.H.{u} ((SheafOfModules.toSheaf.{u} R).obj F) n) : x = 0 :=
  have := (isZero_hgroupTop_iff_subsingleton_sheafH R n F).1 h
  Subsingleton.elim x 0

end RingedSpace

section Scheme

variable (X : Scheme.{u})
  [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

/-- **Cohomology over `⊤` of a module on a scheme is global abelian sheaf cohomology.** -/
def schemeHgroupTopIsoSheafH (n : ℕ) (F : X.Modules) :
    Hgroup X.ringCatSheaf ⊤ n F ≅
      AddCommGrpCat.of (Sheaf.H.{u} ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) n) :=
  hgroupTopIsoSheafH X.ringCatSheaf n F

/-- The comparison `schemeHgroupTopIsoSheafH`, read as an additive equivalence of the underlying
groups. -/
def schemeHgroupTopAddEquivSheafH (n : ℕ) (F : X.Modules) :
    Hgroup X.ringCatSheaf ⊤ n F ≃+
      Sheaf.H.{u} ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) n :=
  hgroupTopAddEquivSheafH X.ringCatSheaf n F

/-- **The two models of the global cohomology of a module on a scheme vanish together.** -/
theorem isZero_schemeHgroupTop_iff_subsingleton_sheafH (n : ℕ) (F : X.Modules) :
    IsZero (Hgroup X.ringCatSheaf ⊤ n F) ↔
      Subsingleton (Sheaf.H.{u} ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) n) :=
  isZero_hgroupTop_iff_subsingleton_sheafH X.ringCatSheaf n F

/-- **Vanishing of the global cohomology of a module on a scheme, computed in `Mod(𝒪_X)`, kills
every global cohomology class of the underlying abelian sheaf.** -/
theorem eq_zero_sheafH_of_isZero_schemeHgroupTop (n : ℕ) (F : X.Modules)
    (h : IsZero (Hgroup X.ringCatSheaf ⊤ n F))
    (x : Sheaf.H.{u} ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) n) : x = 0 :=
  eq_zero_sheafH_of_isZero_hgroupTop X.ringCatSheaf n F h x

end Scheme

end Stacks.Cohomology.ModuleComparison

end
