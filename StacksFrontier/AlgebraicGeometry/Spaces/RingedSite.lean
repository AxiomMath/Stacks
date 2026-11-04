module

public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentOnSite
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite

/-!
# The small étale ringed site of an algebraic space

The small étale site of an algebraic space `F` over a scheme `S`, together with the structure
sheaf of global regular functions on its étale charts, is a ringed site. Quasi-coherent sheaves
on `F` are the quasi-coherent sheaves of modules on that ringed site.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleRingedSite` is the small étale site of `F` with its
  structure sheaf, as an `AlgebraicGeometry.RingedSite`.
* `AlgebraicGeometry.Space.Modules` is the category of sheaves of modules on that ringed site.
* `AlgebraicGeometry.Space.QuasicoherentSheaves` is the full subcategory `QCoh(𝒪_F)` of the
  quasi-coherent ones.

## Main results

* `AlgebraicGeometry.Space.smallEtaleRingedSite_hasWeakSheafify_over`: every slice of the small
  étale ringed site admits sheafification of presheaves of abelian groups.
* `AlgebraicGeometry.Space.smallEtaleRingedSite_wEqualsLocallyBijective_over`: on every slice of
  the small étale ringed site, the local equivalences of presheaves of abelian groups are the
  locally bijective morphisms.

## References

* [Stacks Project, Tag 03G9](https://stacks.math.columbia.edu/tag/03G9)
* [Stacks Project, Tag 04KH](https://stacks.math.columbia.edu/tag/04KH)
-/

@[expose] public section

open CategoryTheory

universe u m

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- The small étale site of the algebraic space `F`, endowed with its structure sheaf of
global regular functions, as a ringed site `(F_étale, 𝒪_F)`. -/
def smallEtaleRingedSite (hF : IsAlgebraicSpace B S hS F) : RingedSite.{u + 1, u, u} where
  C := SmallEtale B S hS F
  J := SmallEtale.topology B S hS F
  O := structureSheaf B S hS F hF

/-- Every slice of the small étale ringed site of `F` admits sheafification of presheaves of
abelian groups. -/
instance smallEtaleRingedSite_hasWeakSheafify_over (hF : IsAlgebraicSpace B S hS F) :
    ∀ U : (smallEtaleRingedSite B S hS F hF).C,
      HasWeakSheafify ((smallEtaleRingedSite B S hS F hF).J.over U) AddCommGrpCat.{u} := by
  change ∀ U : SmallEtale B S hS F,
    HasWeakSheafify ((SmallEtale.topology B S hS F).over U) AddCommGrpCat.{u}
  infer_instance

/-- On every slice of the small étale ringed site of `F`, the local equivalences of presheaves
of abelian groups are exactly the locally bijective morphisms. -/
instance smallEtaleRingedSite_wEqualsLocallyBijective_over (hF : IsAlgebraicSpace B S hS F) :
    ∀ U : (smallEtaleRingedSite B S hS F hF).C,
      ((smallEtaleRingedSite B S hS F hF).J.over U).WEqualsLocallyBijective
        AddCommGrpCat.{u} := by
  change ∀ U : SmallEtale B S hS F,
    ((SmallEtale.topology B S hS F).over U).WEqualsLocallyBijective AddCommGrpCat.{u}
  infer_instance

/-- Sheaves of modules on the small étale ringed site of the algebraic space `F`, that is,
`𝒪_F`-modules. The universe of the module sections is independent of the universe of the
schemes. -/
noncomputable abbrev Modules (hF : IsAlgebraicSpace B S hS F) := SheafOfModules.{m}
  ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))

/-- The category `QCoh(𝒪_F)` of quasi-coherent sheaves on the algebraic space `F`: the full
subcategory of the `𝒪_F`-modules cut out by quasi-coherence on the small étale ringed site. -/
@[stacks 03G9]
noncomputable abbrev QuasicoherentSheaves (hF : IsAlgebraicSpace B S hS F) :=
  (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, m}
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).FullSubcategory

end AlgebraicGeometry.Space

end
