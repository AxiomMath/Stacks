module

public import StacksFrontier.AlgebraicGeometry.Cohomology.LocallyNoetherian.Coherent
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.CoherentCategory
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.SheafHomReflexive
public import StacksFrontier.AlgebraicGeometry.ReflexiveHull.StructureSheaf

/-!
# Internal Hom and duals of coherent reflexive modules

Let `X` be an integral locally Noetherian scheme and `𝒞` the category of coherent reflexive
`𝒪_X`-modules.  The sheaf Hom `ℋom_{𝒪_X}(𝒢, ℋ)` of two objects of `𝒞` is again coherent — by
[Stacks, Tag 01Y2] — and reflexive — by [Stacks, Tag 0AY4], because `ℋ` is.  So `𝒞` has an
internal Hom, computed in `Coh(𝒪_X)` with no hull correction.  Taking `ℋ = 𝒪_X`, which is itself
a coherent reflexive module, gives every object of `𝒞` a dual object.

## Main definitions

* `unitObj X`: the structure sheaf, as a coherent reflexive module.
* `internalHomObj G H`: the sheaf Hom `ℋom_{𝒪_X}(𝒢, ℋ)`, as a coherent reflexive module.
* `dualObj F`: the dual object `ℋom_{𝒪_X}(ℱ, 𝒪_X)` of `ℱ` in `𝒞`.
* `homEquiv₂`, `homEquivCoh`: the identifications of morphisms of `𝒞`, respectively of
  morphisms from a coherent module into one of `𝒞`, with morphisms of the underlying
  `𝒪_X`-modules.

## Main results

The underlying `𝒪_X`-module of `internalHomObj G H` is the sheaf Hom
(`internalHomObj_obj_obj`), and that of `dualObj F` is the dual sheaf
(`dualObj_obj_obj`); so these are the Stacks Project's objects and not merely isomorphic ones.

## References

* [Stacks Project, Tag 0EBH](https://stacks.math.columbia.edu/tag/0EBH)
-/

@[expose] public section

attribute [local implicit_reducible] TopCat.Presheaf.IsSheaf

open CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ReflexiveModules (IsReflexive dualSheaf isReflexive_unit unitModule)
open Stacks.AlgebraicGeometry.ReflexiveHull (CoherentModules CoherentReflexiveModules inclusion)
open Stacks.SheafOfModules.InternalHom (isCoherent_sheafInternalHom' sheafInternalHom
  spaceRingedSite)

universe u

namespace AlgebraicGeometry.CoherentReflexive

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- A morphism of coherent reflexive modules is a morphism of the underlying `𝒪_X`-modules. -/
def homEquiv₂ (A B : CoherentReflexiveModules X) : (A ⟶ B) ≃ (A.obj.obj ⟶ B.obj.obj) where
  toFun f := f.hom.hom
  invFun f := ObjectProperty.homMk (ObjectProperty.homMk f)
  left_inv _ := rfl
  right_inv _ := rfl

/-- A morphism from a coherent module into a coherent reflexive one is a morphism of the
underlying `𝒪_X`-modules. -/
noncomputable def homEquivCoh (T : CoherentModules X) (B : CoherentReflexiveModules X) :
    (T ⟶ (inclusion X).obj B) ≃ (T.obj ⟶ B.obj.obj) where
  toFun f := f.hom
  invFun f := ObjectProperty.homMk f
  left_inv _ := rfl
  right_inv _ := rfl

/-- The structure sheaf, as a coherent reflexive module.  It is coherent by [Stacks, Tag 01XZ]
and reflexive because it is its own dual. -/
noncomputable abbrev unitObj (X : Scheme.{u}) [IsLocallyNoetherian X] :
    CoherentReflexiveModules X :=
  ⟨⟨unitModule X, Stacks.AlgebraicGeometry.CoherentTFAE.structureSheaf_isCoherent X⟩,
    isReflexive_unit X⟩

/-- **Stacks Project, Tag 0EBH.**  The sheaf Hom of two coherent reflexive modules, as a
coherent reflexive module: it is coherent by [Stacks, Tag 01Y2] and reflexive by
[Stacks, Tag 0AY4]. -/
@[stacks 0EBH "internal_hom"]
noncomputable def internalHomObj (G H : CoherentReflexiveModules X) :
    CoherentReflexiveModules X :=
  have : _root_.SheafOfModules.IsCoherent G.obj.obj := G.obj.property
  have coherentTarget : _root_.SheafOfModules.IsCoherent H.obj.obj := H.obj.property
  have finitePresentation : G.obj.obj.IsFinitePresentation := isFinitePresentation_of_isCoherent _
  ⟨⟨sheafInternalHom (spaceRingedSite X.sheaf) G.obj.obj H.obj.obj,
      @isCoherent_sheafInternalHom' _ _ X.sheaf G.obj.obj H.obj.obj
        finitePresentation coherentTarget⟩,
    sheafHom_isReflexive X G.obj.obj H.obj.obj H.property⟩

/-- The underlying `𝒪_X`-module of the internal Hom is the sheaf Hom. -/
theorem internalHomObj_obj_obj (G H : CoherentReflexiveModules X) :
    (internalHomObj G H).obj.obj =
      sheafInternalHom (spaceRingedSite X.sheaf) G.obj.obj H.obj.obj :=
  rfl

/-- **Stacks Project, Tag 0EBH.**  Every coherent reflexive module has a dual object in the
category of coherent reflexive modules, namely `ℋom_{𝒪_X}(ℱ, 𝒪_X)`. -/
@[stacks 0EBH "dual"]
noncomputable def dualObj (F : CoherentReflexiveModules X) : CoherentReflexiveModules X :=
  internalHomObj F (unitObj X)

/-- The underlying `𝒪_X`-module of the dual object is the dual sheaf. -/
theorem dualObj_obj_obj (F : CoherentReflexiveModules X) :
    (dualObj F).obj.obj = dualSheaf F.obj.obj :=
  rfl

end AlgebraicGeometry.CoherentReflexive

end
