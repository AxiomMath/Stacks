module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FpqcTopology.QuasicoherentFpqcSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.FinerTopologies
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The associated module of a quasi-coherent sheaf on a site coarser than the fpqc site

Let `S` be a scheme and `F` a quasi-coherent `𝒪_S`-module.  [Stacks, Tag 03OG] builds the sheaf
of modules `Fᵃ` on the big fpqc site of `S`, whose sections over `f : T ⟶ S` are `Γ(T, f⁺ F)`.
The presheaf underlying `Fᵃ`, and its module structure over the presheaf `𝒪` of global
functions, mention no topology at all: they are
`Stacks.Sites.associatedModulePresheaf S F (𝟭 (Over S))`.  So `Fᵃ` is a sheaf on any site of
schemes over `S` whose coverings are fpqc coverings, with the same sections and the same
restriction maps and no sheafification.

This file records that transport in the two forms it is needed in.  The first is restriction
along a functor `toOver : C ⥤ Over S` presenting a site of schemes over `S`, continuous for the
fpqc topology; this is the form that applies to the *chosen* big `τ`-sites of `S` and to the
small étale site, none of which is the full slice `Over S`, and which are the sites carrying
the cohomology of [Stacks, Tag 03P2].  The second is the special case of the full slice itself
equipped with a topology coarser than the fpqc one.

## Main definitions

* `Stacks.EtaleCohomology.structureSheafOfIsContinuous` and
  `Stacks.EtaleCohomology.associatedModuleOfIsContinuous`: the structure sheaf `𝒪` and the
  sheaf of `𝒪`-modules `Fᵃ` on a site of schemes over `S` presented by a functor continuous for
  the fpqc topology.
* `Stacks.EtaleCohomology.structureSheafOfLE` and
  `Stacks.EtaleCohomology.associatedModuleOfLE`: the same on the full slice `Over S` carrying
  the localisation of a topology coarser than the fpqc topology.

## Main results

* `Stacks.EtaleCohomology.isSheaf_associatedPresheaf_of_isContinuous`: the presheaf underlying
  `Fᵃ` satisfies the sheaf condition on any such site.
* `Stacks.EtaleCohomology.isSheaf_associatedPresheaf_of_le`: the same for the localisation at
  `S` of a topology coarser than the fpqc topology.
* `Stacks.EtaleCohomology.isSheaf_structurePresheaf_of_isContinuous` and
  `Stacks.EtaleCohomology.isSheaf_structurePresheaf_of_le`: the corresponding statements for
  the presheaf of global functions.

## Implementation notes

The continuous form is `CategoryTheory.Functor.op_comp_isSheaf_of_isSheaf`, which holds for an
arbitrary coefficient category, applied to the fpqc sheaf conditions of [Stacks, Tag 03OG].  The
coarsening form is `CategoryTheory.Presheaf.IsSheaf.of_le` together with
`Stacks.Sites.over_mono`, the monotonicity of localisation; its hypothesis is
`J ≤ Scheme.fpqcTopology` for a topology `J` on all of `Scheme.{u}`, which is the shape in which
the library's other "one statement, five topologies" results take it, so that each of the five
is recovered by supplying the corresponding comparison
(`AlgebraicGeometry.Scheme.zariskiTopology_le_fpqcTopology` and its four companions).

No `@[stacks]` attribute is attached.  The content being transported is the sheaf condition of
[Stacks, Tag 03OG], and neither that tag nor [Stacks, Tag 03DT] is a statement about restricting
to a coarser site.

## References

* [Stacks Project, Tag 03OG](https://stacks.math.columbia.edu/tag/03OG)
* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
* [Stacks Project, Tag 03DT](https://stacks.math.columbia.edu/tag/03DT)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03P2](https://stacks.math.columbia.edu/tag/03P2)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

variable (S : Scheme.{u}) (F : S.Modules) [F.IsQuasicoherent]

/-! ### Restriction along a continuous functor into the schemes over `S` -/

section Continuous

variable {C : Type (u + 1)} [Category.{u} C] (toOver : C ⥤ Over S)
  (K : GrothendieckTopology C)
  [toOver.IsContinuous K (Scheme.fpqcTopology.{u}.over S)]

/-- Global functions are a sheaf of rings on any site of schemes over `S` presented by a
functor continuous for the fpqc topology, since restriction along a continuous functor carries
sheaves to sheaves. -/
@[sga "4 VIII 4.3" "more general"]
public theorem isSheaf_structurePresheaf_of_isContinuous :
    Presheaf.IsSheaf K (Stacks.Sites.structurePresheaf S toOver) :=
  toOver.op_comp_isSheaf_of_isSheaf _ _ _ (isSheaf_fpqcStructurePresheaf S)

/-- The presheaf `Fᵃ : (f : T ⟶ S) ↦ Γ(T, f⁺ F)` of [Stacks, Tag 03OG] satisfies the sheaf
condition on any site of schemes over `S` presented by a functor continuous for the fpqc
topology.  This is the form that applies to the chosen big `τ`-sites and to the small étale
site, neither of which is the full slice `Over S`. -/
public theorem isSheaf_associatedPresheaf_of_isContinuous :
    Presheaf.IsSheaf K (Stacks.Sites.associatedPresheaf S F toOver) :=
  toOver.op_comp_isSheaf_of_isSheaf _ _ _ (quasiCoherentPresheaf_isSheaf_fpqc' S F)

/-- The structure sheaf `𝒪` of a site of schemes over `S` presented by a functor continuous for
the fpqc topology.  Its sections over an object are the global functions on the underlying
scheme. -/
@[sga "4 VII 2.1" "special case", sga "4 VIII 4.3" "more general"]
public def structureSheafOfIsContinuous : Sheaf K RingCat.{u} :=
  Stacks.Sites.siteStructureSheaf S toOver K
    (isSheaf_structurePresheaf_of_isContinuous S toOver K)

/-- The associated module `Fᵃ` of a quasi-coherent module `F` on `S`, as a sheaf of
`𝒪`-modules on a site of schemes over `S` presented by a functor continuous for the fpqc
topology.  Its sections over an object are the global sections of the pullback of `F` to the
underlying scheme, and no sheafification occurs.

Instantiated at the chosen big `τ`-sites of `S` and at the small étale site, this is the sheaf
whose cohomology is the right-hand side of [Stacks, Tag 03P2]. -/
public def associatedModuleOfIsContinuous :
    SheafOfModules.{u} (structureSheafOfIsContinuous S toOver K) :=
  Stacks.Sites.siteAssociatedModule S F toOver K
    (isSheaf_structurePresheaf_of_isContinuous S toOver K)
    (isSheaf_associatedPresheaf_of_isContinuous S F toOver K)

/-- The underlying abelian presheaf of `Fᵃ` on such a site is the restriction along `toOver` of
the presheaf of pullback sections of [Stacks, Tag 03DS]. -/
@[simp]
public theorem associatedModuleOfIsContinuous_presheaf :
    (associatedModuleOfIsContinuous S F toOver K).val.presheaf =
      Stacks.Sites.associatedPresheaf S F toOver := rfl

end Continuous

/-! ### The full slice at a topology coarser than the fpqc topology -/

section Coarser

variable {J : GrothendieckTopology Scheme.{u}} (hJ : J ≤ Scheme.fpqcTopology.{u})

include hJ

/-- Global functions on the schemes over `S` are a sheaf of rings for the localisation at `S` of
any topology coarser than the fpqc topology: they are an fpqc sheaf, and a sheaf for a finer
topology is a sheaf for a coarser one. -/
public theorem isSheaf_structurePresheaf_of_le :
    Presheaf.IsSheaf (J.over S) (fpqcStructurePresheaf S) :=
  (isSheaf_fpqcStructurePresheaf S).of_le (Stacks.Sites.over_mono hJ S)

/-- The structure sheaf `𝒪` of the big `J`-site of `S` for a topology `J` coarser than the fpqc
topology, as a sheaf of rings.  Its sections over `f : T ⟶ S` are exactly `Γ(T, 𝒪_T)`. -/
@[sga "4 VII 2.1" "special case"]
public def structureSheafOfLE : Sheaf (J.over S) RingCat.{u} :=
  Stacks.Sites.siteStructureSheaf S (𝟭 (Over S)) _ (isSheaf_structurePresheaf_of_le S hJ)

/-- The underlying presheaf of the structure sheaf of the big `J`-site is the presheaf of global
functions. -/
@[simp]
public theorem structureSheafOfLE_obj :
    (structureSheafOfLE S hJ).obj = fpqcStructurePresheaf S := rfl

/-- The presheaf `Fᵃ : (f : T ⟶ S) ↦ Γ(T, f⁺ F)` of [Stacks, Tag 03OG] satisfies the sheaf
condition for the localisation at `S` of any topology coarser than the fpqc topology. -/
public theorem isSheaf_associatedPresheaf_of_le :
    Presheaf.IsSheaf (J.over S) (Stacks.Sites.associatedPresheaf S F (𝟭 (Over S))) :=
  (isSheaf_fpqcAssociatedPresheafOfModules S F).of_le (Stacks.Sites.over_mono hJ S)

/-- The associated module `Fᵃ` of a quasi-coherent module `F` on `S`, as a sheaf of
`𝒪`-modules on the big `J`-site of `S` for a topology `J` coarser than the fpqc topology.  Its
sections over `f : T ⟶ S` are exactly `Γ(T, f⁺ F)`; no sheafification occurs. -/
public def associatedModuleOfLE : SheafOfModules.{u} (structureSheafOfLE S hJ) :=
  Stacks.Sites.siteAssociatedModule S F (𝟭 (Over S)) _
    (isSheaf_structurePresheaf_of_le S hJ) (isSheaf_associatedPresheaf_of_le S F hJ)

/-- The underlying presheaf of modules of `Fᵃ` on the big `J`-site is the one
[Stacks, Tag 03OG] builds, independently of the topology. -/
@[simp]
public theorem associatedModuleOfLE_val :
    (associatedModuleOfLE S F hJ).val = fpqcAssociatedPresheafOfModules S F := rfl

/-- The sections of `Fᵃ` over a scheme `T` over `S` are the global sections of the pullback of
`F` to `T`, for every topology coarser than the fpqc topology. -/
public theorem associatedModuleOfLE_presheaf_obj (T : (Over S)ᵒᵖ) :
    (associatedModuleOfLE S F hJ).val.presheaf.obj T =
      AddCommGrpCat.of Γ((Scheme.Modules.pullback T.unop.hom).obj F, ⊤) := rfl

end Coarser

end Stacks.EtaleCohomology

end
