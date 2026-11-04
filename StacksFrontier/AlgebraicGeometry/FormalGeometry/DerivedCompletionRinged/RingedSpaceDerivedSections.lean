module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomFilteredColimit
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.SliceDerivedSections
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusComparisons
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.DerivedSectionsOverBase

/-!
# The derived sections of a ringed space are the derived global sections of its ringed site

Let `Z` be a ringed space, `A` a commutative ring and `ρ : A ⟶ Γ(𝒞, 𝒪_Z)` a presentation of the
structure sheaf as a sheaf of `A`-algebras on the site of opens of `Z`. There are two functors
called `RΓ(Z, -) : D(𝒪_Z) ⥤ D(A)` in this library:

* `Stacks.Cohomology.DerivedSectionsOverBase.derivedSectionsOver`, the total right derived
  functor of **evaluation at `⊤`** on sheaves of modules on the ringed space `Z`;
* `AlgebraicGeometry.RingedSite.derivedGlobalSectionsOverUnbounded`, the total right derived
  functor of `Hom_𝒪(𝒪, -)` on sheaves of modules on the ringed **site**
  `Stacks.SheafOfModules.opensRingedSite Z.sheaf`.

This file identifies them. The two source categories are the same on the nose — the sheaf of
rings of the ringed site of opens of `Z` *is* `structureSheafRing Z` — and the two underived
functors differ by `AlgebraicGeometry.RingedSite.moduleGlobalSectionsOverIsoSectionsTerminal` at
the terminal object `⊤` of `Opens Z`. The derived-level consequence is the uniqueness of total
right derived functors.

The identification is what lets a statement about derived completion on a ringed site — where
the Čech and Koszul descriptions of `(-)^∧` live — be read against the derived sections of a
ringed space, where the cohomology of a punctured spectrum is computed.

## Main results

* `CategoryTheory.Functor.totalRightDerivedNatIso` — the total right derived functor of a functor
  along a localization depends on that functor only up to isomorphism.
* `Stacks.Cohomology.RingedSpaceSections.siteScalars` — a ring map `A ⟶ Γ(Z, 𝒪_Z)` read as the
  presentation of `𝒪_Z` as a sheaf of `A`-algebras on the site of opens.
* `Stacks.Cohomology.RingedSpaceSections.sectionsOverIsoModuleGlobalSectionsOver` — the underived
  comparison `Γ(Z, -) ≅ Γ(𝒞, -)`, `A`-linearly.
* `Stacks.Cohomology.RingedSpaceSections.derivedSectionsOverIsoDerivedGlobalSectionsOverUnbounded`
  — **the comparison above**, `RΓ(Z, -) ≅ RΓ(𝒞, -)` as functors `D(𝒪_Z) ⥤ D(A)`.

## Implementation notes

*The scalars.* The ringed-space functor takes its scalars along a ring map `A ⟶ 𝒪_Z(⊤)` and the
ringed-site one along a ring map `A ⟶ Γ(𝒞, 𝒪)` into the ring of compatible families of local
sections. On a site with a terminal object the two rings agree, and the comparison is stated at a
`ρ` of the first kind, the second being `Stacks.Cohomology.RingedSpaceSections.siteScalars` —
`AlgebraicGeometry.RingedSite.sectionsRingHomOfTerminal` at `⊤` — whose value at `⊤` is `ρ`
again by `sectionsEval_comp_siteScalars`. So nothing is assumed about the two presentations
matching: one is built from the other.

*Why uniqueness of derived functors is the whole of the derived step.* Both functors are
`CategoryTheory.Functor.totalRightDerived` along `DerivedCategory.Qh` for the quasi-isomorphisms
of the homotopy category of the one category of sheaves of modules, so the isomorphism the two
underived functors induce on homotopy categories —
`CategoryTheory.Functor.mapHomotopyCategoryNatIso` — determines one of the derived ones by
`CategoryTheory.Functor.totalRightDerivedNatIso`, which is
`CategoryTheory.Functor.rightDerivedNatIso` at the two canonical units.

*The two spellings of the category of sheaves of modules.* `structureSheafRing Z` and the sheaf of
rings of the ringed site of opens of `Z` are equal by `rfl`, but an instance proved at one
spelling is not found by a search at the other, the search being syntactic. The comparison is
therefore stated with the ringed-space spelling throughout and the one site-side instance it needs
— additivity of `A`-linear global sections — is restated here with its source category ascribed.
The derived step needs no such bridge, because
`CategoryTheory.Functor.totalRightDerivedNatIso` is stated for an abstract localization: the
instances it consumes are resolved there, where there is only one spelling.

## References

* [Stacks Project, Tag 0BLX](https://stacks.math.columbia.edu/tag/0BLX)
* [Stacks Project, Tag 0D6F](https://stacks.math.columbia.edu/tag/0D6F)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace CategoryTheory.Functor

/-- **The total right derived functor depends on the functor derived only up to isomorphism.**
An isomorphism `F ≅ F'` of functors `C ⥤ H`, both admitting a right derived functor along a
localization `L : C ⥤ D` of `W`, induces an isomorphism of their total right derived functors.

This is `CategoryTheory.Functor.rightDerivedNatIso` at the two canonical units, the
`IsRightDerivedFunctor` instances being the ones `totalRightDerived` carries by construction. -/
noncomputable def totalRightDerivedNatIso {C D H : Type*} [Category* C] [Category* D]
    [Category* H] {F F' : C ⥤ H} (e : F ≅ F') (L : C ⥤ D) (W : MorphismProperty C)
    [L.IsLocalization W] [F.HasRightDerivedFunctor W] [F'.HasRightDerivedFunctor W] :
    F.totalRightDerived L W ≅ F'.totalRightDerived L W :=
  rightDerivedNatIso _ _ (F.totalRightDerivedUnit L W) (F'.totalRightDerivedUnit L W) W e

end CategoryTheory.Functor

namespace Stacks.Cohomology.RingedSpaceSections

attribute [local instance] HasDerivedCategory.standard

variable (Z : RingedSpace.{u, u}) (A : Type u) [CommRing A]
  (ρ : A →+* (structureSheafRing Z).obj.obj (op (⊤ : Opens Z.carrier)))

/-- **The structure sheaf of a ringed space as a sheaf of `A`-algebras on its site of opens.**
A ring map `A ⟶ Γ(Z, 𝒪_Z)` read as a ring map into the compatible families of local sections,
which is the form `AlgebraicGeometry.RingedSite.moduleGlobalSectionsOver` asks for: this is
`AlgebraicGeometry.RingedSite.sectionsRingHomOfTerminal` at the terminal object `⊤` of
`Opens Z`. -/
abbrev siteScalars : A →+* RingCat.sectionsSubring
    ((Stacks.SheafOfModules.Tensor.ringSheaf
      (Stacks.SheafOfModules.opensRingedSite Z.sheaf).O)).obj :=
  (RingedSite.sectionsRingHomOfTerminal
    (Stacks.SheafOfModules.opensRingedSite Z.sheaf) (T := (⊤ : Opens Z.carrier))
    isTerminalTop).comp ρ

/-- The value at `⊤` of the global section that
`AlgebraicGeometry.RingedSite.sectionsRingHomOfTerminal` attaches to a section over `⊤` is that
section again, so `Stacks.Cohomology.RingedSpaceSections.siteScalars` carries the same scalars
as the ring map it is built from. -/
theorem sectionsEval_comp_siteScalars :
    (RingedSite.sectionsEval (X := Stacks.SheafOfModules.opensRingedSite Z.sheaf) (op ⊤)).comp
      (siteScalars Z A ρ) = ρ := by
  have h := RingedSite.sectionsEval_comp_sectionsRingHomOfTerminal
    (Stacks.SheafOfModules.opensRingedSite Z.sheaf) (T := (⊤ : Opens Z.carrier)) isTerminalTop
  exact RingHom.ext fun a ↦ RingHom.congr_fun h (ρ a)

/-- **Sections over `⊤` of a sheaf of modules on a ringed space are its global sections on the
site of opens**, `A`-linearly. This is
`AlgebraicGeometry.RingedSite.moduleGlobalSectionsOverIsoSectionsTerminal` at the terminal object
`⊤` of `Opens Z`; the categories of sheaves of modules on the two sides are the same, the sheaf
of rings of the ringed site of opens of `Z` being `structureSheafRing Z`. -/
def sectionsOverIsoModuleGlobalSectionsOver :
    DerivedSectionsOverBase.sectionsOver Z ρ ≅
      RingedSite.moduleGlobalSectionsOver
        (Stacks.SheafOfModules.opensRingedSite Z.sheaf) A (siteScalars Z A ρ) :=
  eqToIso (congrArg
      (RingedSite.moduleSectionsOver (Stacks.SheafOfModules.opensRingedSite Z.sheaf)
        (⊤ : Opens Z.carrier))
      (sectionsEval_comp_siteScalars Z A ρ).symm) ≪≫
    (RingedSite.moduleGlobalSectionsOverIsoSectionsTerminal
      (Stacks.SheafOfModules.opensRingedSite Z.sheaf) A (siteScalars Z A ρ) isTerminalTop).symm

/-- **Additivity of `A`-linear global sections on the site of opens, at the ringed-space
spelling of the category of sheaves of modules.** The two spellings of the category are the same
by `rfl`, but an instance proved at one of them does not fire at the other, because the
`Preadditive` instance in the statement of `CategoryTheory.Functor.Additive` is found by a
syntactic search. This is `AlgebraicGeometry.RingedSite.moduleGlobalSectionsOver_additive` with
the source category ascribed. -/
local instance moduleGlobalSectionsOverAdditiveOfRingedSpace :
    (show SheafOfModules.{u} (structureSheafRing Z) ⥤ ModuleCat.{u} A from
      RingedSite.moduleGlobalSectionsOver
        (Stacks.SheafOfModules.opensRingedSite Z.sheaf) A (siteScalars Z A ρ)).Additive :=
  RingedSite.moduleGlobalSectionsOver_additive
    (Stacks.SheafOfModules.opensRingedSite Z.sheaf) A (siteScalars Z A ρ)

/-- **The derived sections of a ringed space are the derived global sections of its ringed site**:
`RΓ(Z, -) ≅ RΓ(𝒞, -)` as functors `D(𝒪_Z) ⥤ D(A)`, where on the left `RΓ(Z, -)` is the total
right derived functor of sections over `⊤` on the ringed space `Z` and on the right it is the
total right derived functor of `A`-linear global sections on the site of opens of `Z`.

Both are total right derived functors along `DerivedCategory.Qh`, by the instances
`Stacks.Cohomology.DerivedSectionsOverBase.derivedSectionsOver_isRightDerivedFunctor` and
`AlgebraicGeometry.RingedSite.derivedGlobalSectionsOverUnbounded_isRightDerivedFunctor`, so the
isomorphism of the underived functors determines one of the derived ones by
`CategoryTheory.Functor.rightDerivedNatIso`. -/
def derivedSectionsOverIsoDerivedGlobalSectionsOverUnbounded :
    DerivedSectionsOverBase.derivedSectionsOver Z ρ ≅
      RingedSite.derivedGlobalSectionsOverUnbounded
        (Stacks.SheafOfModules.opensRingedSite Z.sheaf) A (siteScalars Z A ρ) :=
  Functor.totalRightDerivedNatIso
    (Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryNatIso (sectionsOverIsoModuleGlobalSectionsOver Z A ρ)
        (ComplexShape.up ℤ))
      DerivedCategory.Qh)
    DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Z)) (ComplexShape.up ℤ))

end Stacks.Cohomology.RingedSpaceSections

end
