module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.Comparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.VanishingOnCofinalCoverings
public import StacksFrontier.Homology.CompositeCollapse

/-!
# Affine objects, standard coverings and global sections of a chosen big site

Let `S` be a scheme and let `B` be a chosen big `τ`-site `(Sch/S)_τ` over `S`. This module
records the collections of objects and coverings that the cohomology of an adequate module on
`B` is computed with, and the global-sections functors on `B` and on the small Zariski site of
`S`, in terms of which [Stacks, Tag 06VM] (3) and (4) are stated.

## Main definitions

* `Stacks.Adequate.BigSite.affineObjects` — the affine objects of a chosen big site, the
  collection `B` of [Stacks, Tag 03F9] used in the source's proof of [Stacks, Tag 06VM] (3).
* `Stacks.Adequate.BigSite.standardAffineCov` — the standard affine `τ`-coverings of an object
  of the site, in the sense of [Stacks, Tag 03X9].
* `Stacks.Adequate.BigSite.StandardCovCofinal` — cofinality of those coverings, proved as
  `Stacks.Adequate.BigSite.standardAffineCovCofinal`.
* `Stacks.Adequate.BigSite.globalSections` and `Stacks.Adequate.zariskiGlobalSections` — global
  sections on the big site and on the small Zariski site of `S`.

## Main results

* `Stacks.Adequate.BigSite.isTerminal_opensToBig_top` — the open `⊤ ⊆ S` is carried to a
  terminal object of the big site, so sections over it are global sections.

[Stacks, Tag 06VM] (3) itself is
`Stacks.Adequate.BigSite.isZero_rightDerived_sections_of_isAdequate`, and (4) is
`Stacks.Adequate.BigSite.adequateCohomologyIso`.

## References

* [Stacks Project, Tag 06VM](https://stacks.math.columbia.edu/tag/06VM)
* [Stacks Project, Tag 03F9](https://stacks.math.columbia.edu/tag/03F9)
* [Stacks Project, Tag 03FI](https://stacks.math.columbia.edu/tag/03FI)
* [Stacks Project, Tag 06VL](https://stacks.math.columbia.edu/tag/06VL)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03X9](https://stacks.math.columbia.edu/tag/03X9)
* [Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe x u

namespace Stacks.Adequate

variable {τ : CoveringTopology} {S : Scheme.{u}}

/-! ### Affine objects and their standard affine coverings -/

/-- The affine objects of a chosen big site over `S`: those whose underlying scheme is affine.
This is the collection `B` to which [Stacks, Tag 03F9] is applied in the source's proof of
[Stacks, Tag 06VM] (3). -/
public def BigSite.affineObjects (B : BigSite τ S) : Set B.category :=
  {U | IsAffine U.left.obj}

/-- The standard affine `τ`-coverings of an object `U` of a chosen big site over `S`: the
coverings of `U` whose underlying family of scheme morphisms is a standard affine covering in
the sense of [Stacks, Tag 03X9]. This is the collection `Cov` to which [Stacks, Tag 03F9] is
applied in the source's proof of [Stacks, Tag 06VM] (3). -/
public def BigSite.standardAffineCov (B : BigSite τ S) (U : B.category) :
    Set { E : PreZeroHypercover.{u} U // E.sieve₀ ∈ B.topology U } :=
  { E | ∃ h : IsAffine U.left.obj,
      @IsStandardCovering τ U.left.obj h E.1.I₀ (fun i ↦ (E.1.X i).left.obj)
        (fun i ↦ (E.1.f i).left.hom) }

/-- An object carrying a standard affine covering is itself an affine object. -/
public theorem BigSite.mem_affineObjects_of_mem_standardAffineCov (B : BigSite τ S)
    {U : B.category} {E : { E : PreZeroHypercover.{u} U // E.sieve₀ ∈ B.topology U }}
    (hE : E ∈ B.standardAffineCov U) : U ∈ B.affineObjects :=
  hE.elim fun h _ ↦ h

/-- Every covering sieve of an affine object of the site is refined by a standard affine
`τ`-covering. This is the hypothesis `hCovCofinal` of [Stacks, Tag 03F9] at the collection of
standard affine coverings. -/
public abbrev BigSite.StandardCovCofinal (B : BigSite τ S) : Prop :=
  ∀ U ∈ B.affineObjects, ∀ R ∈ B.topology U,
    ∃ E ∈ B.standardAffineCov U,
      (E : { E : PreZeroHypercover.{u} U // E.sieve₀ ∈ B.topology U }).1.sieve₀ ≤ R

/-! ### Global sections on the big site and on the small Zariski site of the base -/

/-- Sections over an object of a site are an additive functor on abelian sheaves. -/
public instance sheafSections_obj_additive {C : Type*} [Category* C]
    {J : GrothendieckTopology C} (A : Type*) [Category* A] [Preadditive A] (U : C) :
    ((sheafSections J A).obj (op U)).Additive :=
  ⟨rfl⟩

/-- Global sections on a chosen big site over `S`: sections over the object given by the open
`⊤ ⊆ S`, which is a terminal object of the site by
`Stacks.Adequate.BigSite.isTerminal_opensToBig_top`. -/
public noncomputable abbrev BigSite.globalSections (B : BigSite τ S) :
    Sheaf B.topology AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
  (sheafSections B.topology AddCommGrpCat.{u}).obj (op (B.opensToBig.obj ⊤))

/-- Global sections on the small Zariski site of `S`: sections over the open `⊤ ⊆ S`. -/
public noncomputable abbrev zariskiGlobalSections (S : Scheme.{u}) :
    Sheaf (Opens.grothendieckTopology ↥S) AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
  (sheafSections (Opens.grothendieckTopology ↥S) AddCommGrpCat.{u}).obj (op (⊤ : S.Opens))

/-- **The open `⊤ ⊆ S` is a terminal object of a chosen big site over `S`.** Its structure
morphism is the open immersion of `⊤`, which is an isomorphism by
`AlgebraicGeometry.Scheme.topIso`, and an object of a slice category whose structure morphism is
an isomorphism is terminal. -/
public noncomputable def BigSite.isTerminal_opensToBig_top (B : BigSite τ S) :
    IsTerminal (B.opensToBig.obj (⊤ : S.Opens)) := by
  refine IsTerminal.ofIso Over.mkIdTerminal
    (Iso.symm (Over.isoMk (ObjectProperty.isoMk _ (Scheme.topIso S)) ?_))
  apply ObjectProperty.hom_ext
  simp only [Over.mk_hom]
  rfl


end Stacks.Adequate

end
