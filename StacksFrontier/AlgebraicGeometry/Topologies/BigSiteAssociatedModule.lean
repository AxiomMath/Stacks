module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.AssociatedModuleOnCoarserTopologies
public import StacksFrontier.AlgebraicGeometry.Topologies.BigEtaleStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.BigFppfStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.OverSliceContinuity
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSmoothStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSyntomicStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.BigZariskiStructureSheaf

/-!
# The associated module `Fᵃ` on the big `τ`-site, for all five topologies at once

[Stacks, Tag 03DU] (3) attaches to a quasi-coherent `𝒪_S`-module `F` the sheaf of
`𝒪`-modules `Fᵃ` on the big site `(Sch/S)_τ`, defined by its sections: the object
`f : T → S` is sent to `Γ(T, f^* F)`.  Clause (1) of the same definition is the structure
sheaf `𝒪` of that site, and `Fᵃ` is a sheaf of modules over it.

This file builds clause (3) **uniformly in `τ`**, for `τ` ranging over Zariski, étale,
smooth, syntomic and fppf, and identifies the base ring sheaf with the five structure sheaves
of clause (1) that the tree already has.

The two inputs are already in the tree and neither is a hypothesis here:

* the sheaf condition for the presheaf of pullback sections on *all* schemes over `S`, which
  is [Stacks, Tag 03DT], proved unconditionally as
  `AlgebraicGeometry.quasiCoherentPresheaf_isSheaf_fpqc'`;
* continuity of the functor `AlgebraicGeometry.overToSlice` from the localized big `τ`-site
  into the slice of all schemes over `S` for the localized fpqc topology, which is the
  instance `AlgebraicGeometry.isContinuous_overToSlice_fpqc`, uniform in `τ`.

Restriction along a continuous functor carries sheaves to sheaves, so no sheafification occurs
and the sections of `Fᵃ` over an object of the big site are literally `Γ(T, f^* F)`, as the
source demands.

## Main definitions

* `AlgebraicGeometry.overStructureSheaf`: clause (1), the structure sheaf of the localized big
  `τ`-site, uniform in `τ`.
* `AlgebraicGeometry.overAssociatedModule`: **clause (3)**, the associated module `Fᵃ` on the
  big `τ`-site, as a sheaf of modules over that structure sheaf.

## Main results

* `AlgebraicGeometry.isSheaf_overAssociatedPresheaf`: the presheaf of pullback sections
  satisfies the sheaf condition on the localized big `τ`-site, for all five `τ`.
* `AlgebraicGeometry.overStructureSheaf_zariski` and its four companions: the uniform
  structure sheaf is the one each of the five `Big‹τ›Over.structureSheaf` declarations builds.
* `AlgebraicGeometry.overAssociatedModule_presheaf_obj`: the sections of `Fᵃ` over an object
  of the big site are the global sections of the pullback of `F`.

## Implementation notes

The construction is `Stacks.EtaleCohomology.associatedModuleOfIsContinuous`, which is stated
for an arbitrary site of schemes over `S` presented by a functor continuous for the localized
fpqc topology; the only thing supplied here is the presenting functor
`AlgebraicGeometry.overToSlice` of the localized big `τ`-site together with its continuity
instance.  Writing it once rather than five times is possible because
`AlgebraicGeometry.isContinuous_overToSlice_fpqc` is itself uniform in `τ`: the five covering
morphism properties are all contained in flatness together with local finite presentation
(`AlgebraicGeometry.coveringMorphismProperty_le_flat_inf_locallyOfFinitePresentation`).

The five identifications with `Big‹τ›Over.structureSheaf` hold by `rfl`.  The presenting
functor of the localized big site is `CategoryTheory.Over.post` of
`AlgebraicGeometry.schemeBelowInclusion` at the cutoff of the site, which is the spelling the
five clause-(1) files use, and `AlgebraicGeometry.overTopology` is defined by cases to be the
topology of each of them; the sheaf-condition fields then agree by proof irrelevance.

The big fppf case is **not** conditional.  The route through the chosen bounded covering
families needs them stable under base change, which they are not known to be; the route taken
here goes through continuity of `AlgebraicGeometry.overToSlice`, proved from cover preservation
alone, so the fppf case costs exactly what the other four cost.  The hypothesis carried by
`AlgebraicGeometry.BigFppfOver.associatedSheafFunctor` is therefore a theorem, and the
unconditional version is `AlgebraicGeometry.BigFppfOver.associatedSheafFunctorUnconditional`.

## References

* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
* [Stacks Project, Tag 03DT](https://stacks.math.columbia.edu/tag/03DT)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
-/

@[expose] public section

open CategoryTheory Opposite
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable (τ : CoveringTopology) (B : BigSite.{u} τ) (S : Scheme.{u})
  (hS : S.size < cutoff τ B)

/-! ### Clause (1), uniform in `τ` -/

/-- **[Stacks, Tag 03DU] (1), uniform in `τ`.**  The presheaf of global functions is a sheaf of
rings on the localized big `τ`-site: it is an fpqc sheaf on all schemes over `S`, and the
functor into that slice is continuous. -/
public theorem isSheaf_overStructurePresheaf :
    Presheaf.IsSheaf (overTopology τ B S hS)
      (Stacks.Sites.structurePresheaf S (overToSlice τ B S hS)) :=
  Stacks.EtaleCohomology.isSheaf_structurePresheaf_of_isContinuous S (overToSlice τ B S hS)
    (overTopology τ B S hS)

/-- The structure sheaf `𝒪` of the localized big `τ`-site, uniform in `τ`.  Its value at an
object `T/S` of the site is `Γ(T, 𝒪_T)`. -/
public noncomputable def overStructureSheaf : Sheaf (overTopology τ B S hS) RingCat.{u} :=
  Stacks.EtaleCohomology.structureSheafOfIsContinuous S (overToSlice τ B S hS)
    (overTopology τ B S hS)

/-- The underlying presheaf of the uniform structure sheaf is the presheaf of global
functions. -/
@[simp]
public theorem overStructureSheaf_obj :
    (overStructureSheaf τ B S hS).obj =
      Stacks.Sites.structurePresheaf S (overToSlice τ B S hS) :=
  rfl

/-! #### The uniform structure sheaf is the one each clause-(1) file builds -/

/-- At `τ = zariski` the uniform structure sheaf is
`AlgebraicGeometry.BigZariskiOver.structureSheaf`. -/
public theorem overStructureSheaf_zariski (B : BigZariskiSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    overStructureSheaf .zariski B S hS = BigZariskiOver.structureSheaf B S hS :=
  rfl

/-- At `τ = etale` the uniform structure sheaf is
`AlgebraicGeometry.BigEtaleOver.structureSheaf`. -/
public theorem overStructureSheaf_etale (B : BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    overStructureSheaf .etale B S hS = BigEtaleOver.structureSheaf B S hS :=
  rfl

/-- At `τ = smooth` the uniform structure sheaf is
`AlgebraicGeometry.BigSmoothOver.structureSheaf`. -/
public theorem overStructureSheaf_smooth (B : BigSmoothSite.{u}) (S : Scheme.{u})
    (hS : S.size < B.cutoff) :
    overStructureSheaf .smooth B S hS = BigSmoothOver.structureSheaf B S hS :=
  rfl

/-- At `τ = syntomic` the uniform structure sheaf is
`AlgebraicGeometry.BigSyntomicOver.structureSheaf`. -/
public theorem overStructureSheaf_syntomic (B : BigSyntomicSite.{u}) (S : Scheme.{u})
    (hS : S.size < B.cutoff) :
    overStructureSheaf .syntomic B S hS = BigSyntomicOver.structureSheaf B S hS :=
  rfl

/-- At `τ = fppf` the uniform structure sheaf is
`AlgebraicGeometry.BigFppfOver.structureSheaf`. -/
public theorem overStructureSheaf_fppf (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    overStructureSheaf .fppf B S hS = BigFppfOver.structureSheaf B S hS :=
  rfl

/-! ### Clause (3), uniform in `τ` -/

variable (F : S.Modules) [F.IsQuasicoherent]

/-- **The sheaf condition of [Stacks, Tag 03DU] (3), uniform in `τ`.**  The presheaf
`(f : T → S) ↦ Γ(T, f^* F)` of [Stacks, Tag 03DS] satisfies the sheaf condition on the
localized big `τ`-site: it is an fpqc sheaf on all schemes over `S` by [Stacks, Tag 03DT], and
the functor into that slice is continuous. -/
@[stacks 03DU "part (3), the sheaf condition for `Fᵃ`"]
public theorem isSheaf_overAssociatedPresheaf :
    Presheaf.IsSheaf (overTopology τ B S hS)
      (Stacks.Sites.associatedPresheaf S F (overToSlice τ B S hS)) :=
  Stacks.EtaleCohomology.isSheaf_associatedPresheaf_of_isContinuous S F (overToSlice τ B S hS)
    (overTopology τ B S hS)

/-- **[Stacks, Tag 03DU] (3), uniform in `τ`.**  The associated module `Fᵃ` of a quasi-coherent
`𝒪_S`-module `F` on the big `τ`-site of `S`, as a sheaf of modules over the structure sheaf of
clause (1).  Its sections over an object `f : T → S` of the site are the global sections
`Γ(T, f^* F)`, and no sheafification occurs. -/
@[stacks 03DU "part (3)"]
public noncomputable def overAssociatedModule :
    SheafOfModules.{u} (overStructureSheaf τ B S hS) :=
  Stacks.EtaleCohomology.associatedModuleOfIsContinuous S F (overToSlice τ B S hS)
    (overTopology τ B S hS)

/-- The abelian presheaf underlying `Fᵃ` on the big `τ`-site is the restriction along
`AlgebraicGeometry.overToSlice` of the presheaf of pullback sections of [Stacks, Tag 03DS]. -/
@[simp]
public theorem overAssociatedModule_presheaf :
    (overAssociatedModule τ B S hS F).val.presheaf =
      Stacks.Sites.associatedPresheaf S F (overToSlice τ B S hS) :=
  rfl

/-- **The defining property of `Fᵃ`.**  Its sections over an object `T/S` of the big `τ`-site
are the global sections of the pullback of `F` to `T`. -/
public theorem overAssociatedModule_presheaf_obj (T : (Over (base B S hS))ᵒᵖ) :
    (overAssociatedModule τ B S hS F).val.presheaf.obj T =
      AddCommGrpCat.of
        Γ((Scheme.Modules.pullback ((overToSlice τ B S hS).obj T.unop).hom).obj F, ⊤) :=
  rfl

end AlgebraicGeometry

end
