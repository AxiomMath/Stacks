module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.InverseImageChangeOfRings
public import StacksFrontier.CategoryTheory.Sites.Modules.NaiveCotangentTowerConeMap
public import StacksFrontier.Cotangent.SheavesOfRings.FundamentalTriangle
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Extension of scalars of a short exact sequence with flat third term

Let `h : A ⟶ B` be a homomorphism of sheaves of commutative rings on a small site.  Extension of
scalars along `h`, the sheafified sectionwise tensor product `- ⊗_A B` of
`CategoryTheory.Sheaf.towerExtendScalars`, carries a short exact sequence of sheaves of
`A`-modules whose third term is flat to a short exact sequence of sheaves of `B`-modules.

Applied to the naive cotangent complex `NL_{B/A}` of a locally surjective `A ⟶ B`, whose degree
`0` term is flat (`Stacks.SheafOfModules.isFlat_naiveCotangentComplex_X_zero`) and which sits in
the short exact sequence `Stacks.SheafOfModules.shortExact_conormalSheaf_naiveCotangentComplex`,
this computes `H^{-1}` of `NL_{B/A} ⊗_B D` for any `B ⟶ D`.

## Main results

* `CategoryTheory.Sheaf.towerExtendScalars_additive`: extension of scalars along `h` is additive.
* `CategoryTheory.Sheaf.shortExact_map_towerExtendScalars`: **extension of scalars keeps short
  exact a short exact sequence with flat third term.**

## Implementation notes

This is Stacks 03EX for change of rings,
`Stacks.Sheaves.InverseImageExactness.shortExact_map_extendScalars`, which is stated for the
abstract extension of scalars `Stacks.Sheaves.ModuleAdjunction.extendScalars`, transported along
the identification `Stacks.Sheaves.DerivedPullback.FlatExtendScalars.extendScalarsIsoChangeOfRings`
of that functor with the sheafified sectionwise tensor product.  It lives in its own module
because the instances these imports bring in change the elaboration of the naive cotangent
complex of `StacksFrontier.Cotangent.SheavesOfRings.ConormalSequenceSurjection`.

## References

* [Stacks Project, Tag 03EX](https://stacks.math.columbia.edu/tag/03EX)
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

noncomputable section

namespace CategoryTheory.Sheaf

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  {A B : Sheaf J CommRingCat.{u}} (h : A ⟶ B)

/-- Extension of scalars along `h` is additive, being left adjoint to restriction of scalars.
This is `Stacks.SheafOfModules.towerExtendScalars_additive`, restated at the spelling
`CategoryTheory.Sheaf.towerExtendScalars` so that instance search finds it there. -/
noncomputable instance towerExtendScalars_additive :
    (towerExtendScalars.{u, u, u} J h).Additive :=
  Stacks.SheafOfModules.towerExtendScalars_additive.{u, u, u} J A B h

/-- **Extension of scalars keeps short exact a short exact sequence with flat third term.**  For
a homomorphism `h : A ⟶ B` of sheaves of commutative rings on a small site and a short exact
sequence `S` of sheaves of `A`-modules whose third term is flat, the sequence
`S ⊗_A B` obtained by extending scalars along `h` is short exact.

This is Stacks 03EX for change of rings,
`Stacks.Sheaves.InverseImageExactness.shortExact_map_extendScalars`, transported along the
identification `Stacks.Sheaves.DerivedPullback.FlatExtendScalars.extendScalarsIsoChangeOfRings` of
the abstract extension of scalars with the sheafified sectionwise tensor product. -/
@[sga "4 XVII 4.1.1" "(ii), special case"]
theorem shortExact_map_towerExtendScalars (S : ShortComplex (targetModules.{u, u, u} J A))
    (hS : S.ShortExact) (hflat : AlgebraicGeometry.SheafOfModules.IsFlat S.X₃) :
    (S.map (towerExtendScalars.{u, u, u} J h)).ShortExact := by
  have hS' := Stacks.Sheaves.InverseImageExactness.shortExact_map_extendScalars h S hS hflat
  let τ := Stacks.Sheaves.DerivedPullback.FlatExtendScalars.extendScalarsIsoChangeOfRings h
  exact ShortComplex.shortExact_of_iso
    (ShortComplex.isoMk (τ.app S.X₁) (τ.app S.X₂) (τ.app S.X₃)
      (τ.hom.naturality S.f).symm (τ.hom.naturality S.g).symm) hS'

end CategoryTheory.Sheaf

end
