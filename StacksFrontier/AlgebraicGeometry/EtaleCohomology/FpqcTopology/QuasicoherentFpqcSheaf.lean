module

public import StacksFrontier.AlgebraicGeometry.Descent.FpqcHomSheafRefinement
public import StacksFrontier.AlgebraicGeometry.Topologies.SiteStructureSheaf
public import StacksCore.Tactic.StacksAttribute

/-!
# Quasi-coherent modules give fpqc sheaves of modules on the big site

Let `S` be a scheme and let `F` be a quasi-coherent `𝒪_S`-module.  The presheaf
`Fᵃ : (Sch/S)ᵒᵖ ⥤ Ab` sending a scheme `f : T ⟶ S` over `S` to `Γ(T, f⁺ F)` carries an action of
the ring `Γ(T, 𝒪_T)` of global functions, and this action is compatible with the restriction
maps, so that `Fᵃ` is a module over the structure sheaf `𝒪` of the big fpqc site of `S`.
Moreover `Fᵃ` satisfies the sheaf condition for the fpqc topology, so it is a sheaf of
`𝒪`-modules and not merely a presheaf of them.

## Main definitions

* `Stacks.EtaleCohomology.fpqcStructurePresheaf` and
  `Stacks.EtaleCohomology.fpqcStructureSheaf` are the structure sheaf `𝒪` of the big fpqc site
  of `S`, the sheaf of rings `(f : T ⟶ S) ↦ Γ(T, 𝒪_T)`.
* `Stacks.EtaleCohomology.fpqcAssociatedPresheafOfModules` is `Fᵃ` with its `𝒪`-module
  structure.
* `Stacks.EtaleCohomology.fpqcAssociatedModule` packages the two assertions of the proposition
  into a single sheaf of `𝒪`-modules on the big fpqc site.

## Main results

* `Stacks.EtaleCohomology.isSheaf_fpqcStructurePresheaf`: `𝒪` is a sheaf of rings for the fpqc
  topology.
* `Stacks.EtaleCohomology.isSheaf_fpqcAssociatedPresheafOfModules`: `Fᵃ` satisfies the sheaf
  condition for the fpqc topology.

## Implementation notes

The big fpqc site of `S` is the full slice category `CategoryTheory.Over S` equipped with
`AlgebraicGeometry.Scheme.fpqcTopology.over S`, the localisation at `S` of the fpqc topology on
all schemes; no bound is placed on the schemes appearing as objects.

Both halves of the proposition are instances at this site of constructions available for an
arbitrary site of schemes over `S`, presented by a functor into `CategoryTheory.Over S`; here
that functor is the identity.  The `𝒪`-module structure is
`Stacks.Sites.associatedModulePresheaf`, whose content is the semilinearity
`AlgebraicGeometry.pullbackSectionsMap_smul` of the pullback map on sections over the pullback
map on functions.  The sheaf condition is the fpqc clause of Tag 03DT,
`AlgebraicGeometry.quasiCoherentPresheaf_isSheaf_fpqc'`, which in turn rests on the reduction of
the fpqc sheaf condition to a Zariski condition together with a condition for a faithfully flat
morphism of affine schemes (Tag 03O1,
`Stacks.EtaleCohomology.isSheaf_fpqc_iff_zariski_and_affine_singleton`) and on exactness of the
Amitsur complex with coefficients in a module (Tag 03OA).  The sheaf condition for `𝒪` is the
case `F = 𝒪_S` read through global functions, and is `Stacks.Sites.isSheaf_structurePresheaf`
applied to `Stacks.Sites.isSheaf_fpqcOver_globalSections`.

## References

* [Stacks Project, Tag 03OG](https://stacks.math.columbia.edu/tag/03OG)
* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
* [Stacks Project, Tag 03DT](https://stacks.math.columbia.edu/tag/03DT)
* [Stacks Project, Tag 03O1](https://stacks.math.columbia.edu/tag/03O1)
* [Stacks Project, Tag 03OA](https://stacks.math.columbia.edu/tag/03OA)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

variable (S : Scheme.{u}) (F : S.Modules)

/-! ### The structure sheaf of the big fpqc site -/

/-- The structure presheaf `𝒪` of the big fpqc site of `S`: the presheaf of rings on the schemes
over `S` whose value on `f : T ⟶ S` is the ring `Γ(T, 𝒪_T)` of global functions on `T`, with
restriction maps given by pullback of functions. -/
public abbrev fpqcStructurePresheaf : (Over S)ᵒᵖ ⥤ RingCat.{u} :=
  Stacks.Sites.structurePresheaf S (𝟭 (Over S))

/-- Global functions are a sheaf of rings for the fpqc topology on the schemes over `S`.  They
are a sheaf of types there, and a presheaf of rings whose underlying presheaf of types is a
sheaf is a sheaf of rings. -/
@[sga "4 VII 2.1" "special case"]
public theorem isSheaf_fpqcStructurePresheaf :
    Presheaf.IsSheaf (Scheme.fpqcTopology.{u}.over S) (fpqcStructurePresheaf S) :=
  Stacks.Sites.isSheaf_structurePresheaf S _ _ (Stacks.Sites.isSheaf_fpqcOver_globalSections S)

/-- The structure sheaf `𝒪` of the big fpqc site of `S`, as a sheaf of rings.  No sheafification
occurs: its sections over `f : T ⟶ S` are exactly `Γ(T, 𝒪_T)`. -/
public noncomputable def fpqcStructureSheaf :
    Sheaf (Scheme.fpqcTopology.{u}.over S) RingCat.{u} :=
  Stacks.Sites.siteStructureSheaf S (𝟭 (Over S)) _ (isSheaf_fpqcStructurePresheaf S)

/-- The underlying presheaf of the structure sheaf of the big fpqc site is the presheaf of
global functions. -/
@[simp]
public theorem fpqcStructureSheaf_obj :
    (fpqcStructureSheaf S).obj = fpqcStructurePresheaf S := rfl

/-! ### The associated `𝒪`-module of a quasi-coherent module -/

variable [F.IsQuasicoherent]

/-- **Stacks Project, Tag 03OG**, first assertion.  The presheaf
`Fᵃ : (f : T ⟶ S) ↦ Γ(T, f⁺ F)` attached to a quasi-coherent module `F` on `S` is a module over
the structure presheaf `𝒪` of the big fpqc site of `S`: the sections of `f⁺ F` over `T` form a
module over `Γ(T, 𝒪_T)`, and the restriction maps of `Fᵃ` are semilinear over those of `𝒪`. -/
@[stacks 03OG "F^a is an O-module"]
public noncomputable def fpqcAssociatedPresheafOfModules :
    PresheafOfModules.{u} (fpqcStructurePresheaf S) :=
  Stacks.Sites.associatedModulePresheaf S F (𝟭 (Over S))

/-- The underlying abelian presheaf of `Fᵃ` is the presheaf of pullback sections of Tag 03DS. -/
@[simp]
public theorem fpqcAssociatedPresheafOfModules_presheaf :
    (fpqcAssociatedPresheafOfModules S F).presheaf = quasiCoherentPresheafFunctor S F := rfl

/-- The sections of `Fᵃ` over a scheme `T` over `S` are the global sections of the pullback of
`F` to `T`. -/
public theorem fpqcAssociatedPresheafOfModules_presheaf_obj (T : (Over S)ᵒᵖ) :
    (fpqcAssociatedPresheafOfModules S F).presheaf.obj T =
      AddCommGrpCat.of Γ((Scheme.Modules.pullback T.unop.hom).obj F, ⊤) := rfl

/-- The restriction maps of `Fᵃ` are the pullback maps on global sections. -/
public theorem fpqcAssociatedPresheafOfModules_presheaf_map {T U : (Over S)ᵒᵖ} (g : T ⟶ U) :
    (fpqcAssociatedPresheafOfModules S F).presheaf.map g = pullbackSectionsMap F g.unop := rfl

/-- The `𝒪`-module of sections of `Fᵃ` over a scheme `T` over `S` is the module `Γ(T, f⁺ F)` of
global sections of the pullback of `F`, with its action of the global functions `Γ(T, 𝒪_T)`. -/
public theorem fpqcAssociatedPresheafOfModules_obj (T : (Over S)ᵒᵖ) :
    (fpqcAssociatedPresheafOfModules S F).obj T =
      ModuleCat.of Γ(T.unop.left, ⊤) Γ((Scheme.Modules.pullback T.unop.hom).obj F, ⊤) := rfl

/-- **Stacks Project, Tag 03OG**, second assertion.  The presheaf
`Fᵃ : (f : T ⟶ S) ↦ Γ(T, f⁺ F)` attached to a quasi-coherent module `F` on `S` satisfies the
sheaf condition for the fpqc topology on the schemes over `S`. -/
@[stacks 03OG "the sheaf condition for the fpqc topology"]
public theorem isSheaf_fpqcAssociatedPresheafOfModules :
    Presheaf.IsSheaf (Scheme.fpqcTopology.{u}.over S)
      (fpqcAssociatedPresheafOfModules S F).presheaf :=
  quasiCoherentPresheaf_isSheaf_fpqc' S F

/-- The associated module `Fᵃ` of a quasi-coherent module `F` on `S`, as a sheaf of
`𝒪`-modules on the big fpqc site of `S`.  This packages the two assertions of Tag 03OG; no
sheafification occurs, and the sections over `f : T ⟶ S` are exactly `Γ(T, f⁺ F)`. -/
public noncomputable def fpqcAssociatedModule :
    SheafOfModules.{u} (fpqcStructureSheaf S) :=
  Stacks.Sites.siteAssociatedModule S F (𝟭 (Over S)) _ (isSheaf_fpqcStructurePresheaf S)
    (isSheaf_fpqcAssociatedPresheafOfModules S F)

/-- The underlying presheaf of modules of the sheaf of `𝒪`-modules `Fᵃ`. -/
@[simp]
public theorem fpqcAssociatedModule_val :
    (fpqcAssociatedModule S F).val = fpqcAssociatedPresheafOfModules S F := rfl

end Stacks.EtaleCohomology

end
