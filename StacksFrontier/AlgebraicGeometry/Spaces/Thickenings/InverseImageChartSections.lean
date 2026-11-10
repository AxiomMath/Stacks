module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ConormalModuleInverseImageKernel
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftDifferenceTargetValues
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleChartKernel

/-!
# The inverse image of the structure sheaf along a thickening, on an étale chart

Let `Z ⊆ X` be a thickening of algebraic spaces over a scheme `S` contained in a big fppf site
`B`, with inclusion `i : Z ⟶ X`.  The unit

`η : 𝒪_X ⟶ i_*i^{-1}𝒪_X`

of `i^{-1} ⊣ i_*` is an isomorphism of sheaves of rings
(`AlgebraicGeometry.Space.isIso_ringUnit_of_isThickening`).  This file reads that isomorphism
**on the sections over one étale scheme chart** `V` of `X`: the sections of the inverse image
`i^{-1}𝒪_X` over the chart of `Z` lying under `V` are the regular functions `Γ(V, ⊤)` on `V`,
and the inverse-image form `i^♯ : i^{-1}𝒪_X ⟶ 𝒪_Z` of the structure map of
[Stacks Project, Tag 03G8] is, read through that identification, the direct-image form
`i^♯ : 𝒪_X ⟶ i_*𝒪_Z`.

That is the scheme-level reading of a sheaf on the small étale site of `Z` which the
development has for the *direct* image — the restriction maps of `𝒪_X` are `appTop` of the
underlying morphisms of schemes, by `AlgebraicGeometry.Space.chartRestrict_eq_appTop`, and the
structure map on a chart is `appTop` of the chart base change, by
`AlgebraicGeometry.Space.definingIdealAt_eq_ker` — but not for the *inverse* image, whose
sections are a sheafified colimit and are not definitionally global sections of anything.

Together with
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleChartKernel.lean` this identifies, over an
étale scheme chart `V` of `X` and for a *first-order* thickening, the three descriptions of the
conormal module that the deformation theory uses:

`𝒞_{Z/X}(V) ≅ ker(i^♯ : i^{-1}𝒪_X ⟶ 𝒪_Z)(V) ≅ ker(Γ(V, ⊤) ⟶ Γ(Z ×_X V, ⊤))`,

the last of which is `Stacks.Thickenings.conormalModuleAlong` of the scheme-level theory.

## Main results

* `AlgebraicGeometry.Space.bijective_ringUnit_app_of_isThickening`: **the unit is bijective on
  the sections over every étale chart**, for every sheaf of rings on the small étale site of
  `X`.
* `AlgebraicGeometry.Space.bijective_thickeningRingUnit_app`: the same at the structure sheaf,
  which is the identification of the sections of `i^{-1}𝒪_X` with the regular functions on the
  chart.
* `AlgebraicGeometry.Space.app_ringUnit_comp_map_structureSharpRingInverseImage`: **the two
  forms of the structure map agree through the identification**, read at a section.
* `AlgebraicGeometry.Space.app_structureSharpRingInverseImage_ringUnit_app_eq_zero_iff`: a
  regular function on a chart is killed by the inverse-image form of the structure map, after
  the identification, exactly when it lies in the defining ideal of the thickening at that
  chart.
* `AlgebraicGeometry.Space.app_structureSharpRingInverseImage_ringUnit_app_eq_zero_iff_appTop`:
  **the comparison**, the same condition written as being killed by pullback of regular
  functions along the closed immersion of schemes `Z ×_X V ⟶ V`.

## Implementation notes

**Bijectivity on sections is proved at an abstract site.**  As the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/ConormalModuleInverseImageKernel.lean`
record, instance resolution for `CategoryTheory.IsIso` at a morphism of sheaves of rings on the
small étale site does not terminate, so the invertibility is introduced by name at every call.
The step from invertibility to bijectivity on sections is then a statement about an arbitrary
isomorphism of sheaves of rings on an arbitrary site, `bijective_app_of_isIso` below, where the
terms are small; this is the precaution the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/LiftDifferenceSurjective.lean` describe.

**The two round-trip equations are read at a section with
`AlgebraicGeometry.Space.ringSheafHom_congr_app_apply`**, which gives the composite form, not
the nested one; the nested form is reached by `show`, as for any composite of two morphisms of
sheaves of rings.

**No `@[stacks]` attribute is placed.**  The invertibility of the unit is the equivalence of
the two small étale topoi of a thickening, [Stacks Project, Tag 05ZK], which the imported file
proves and claims no tag for; what is added here is its reading on the sections over a chart.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8), the structure map.
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK), thickenings.
* [Stacks Project, Tag 04CN](https://stacks.math.columbia.edu/tag/04CN), the conormal module.
* [Stacks Project, Tag 0CKE](https://stacks.math.columbia.edu/tag/0CKE), the tag this
  comparison is an input of.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u uu vv

namespace AlgebraicGeometry.Space

/-! ### An isomorphism of sheaves of rings is bijective on sections -/

/-- **An isomorphism of sheaves of rings on any site is bijective on the sections over every
object.**  The two round-trip equations of the isomorphism are inverse functions there.  Stated
at an abstract site, where the terms are small; see the implementation notes. -/
private theorem bijective_app_of_isIso {Cc : Type uu} [Category.{vv} Cc]
    {Jc : GrothendieckTopology Cc} {A Bb : Sheaf Jc RingCat.{u}} (a : A ⟶ Bb) [IsIso a]
    (V : Ccᵒᵖ) : Function.Bijective (a.hom.app V) := by
  have hleft : ∀ x, (inv a).hom.app V (a.hom.app V x) = x :=
    ringSheafHom_congr_app_apply (IsIso.hom_inv_id a) V
  have hright : ∀ y, a.hom.app V ((inv a).hom.app V y) = y :=
    ringSheafHom_congr_app_apply (IsIso.inv_hom_id a) V
  exact ⟨Function.LeftInverse.injective hleft, fun y => ⟨_, hright y⟩⟩

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)

/-! ### The unit on the sections over a chart -/

/-- **The unit `η : O ⟶ i_*i^{-1}O` of the inclusion of a thickening is bijective on the
sections over every étale chart of `X`.**  It is an isomorphism of sheaves of rings by
`AlgebraicGeometry.Space.isIso_ringUnit_of_isThickening`.

So every sheaf of rings on the small étale site of `X` is, chart by chart, the sections of its
inverse image over the chart of `Z` lying under it. -/
theorem bijective_ringUnit_app_of_isThickening (hZ : IsThickening B S hS X Z.1)
    (O : Sheaf (SmallEtale.topology B S hS X.1) RingCat.{u})
    (V : (SmallEtale B S hS X.1)ᵒᵖ) :
    Function.Bijective ((ringUnit (smallToposMorphismTypeU B S hS
      (subspaceInclusion B S hS X Z)) O).hom.app V) :=
  let := isIso_ringUnit_of_isThickening B S hS Z hZ O
  bijective_app_of_isIso _ V

/-- **The sections of `i^{-1}𝒪_X` over the chart of `Z` lying under an étale scheme chart `V` of
`X` are the regular functions on `V`.**  The unit at the structure sheaf is bijective there.

This is the inverse-image counterpart of the definitional identification
`𝒪_X(V) = Γ(V, ⊤)` which `AlgebraicGeometry.Space.chartRestrict_eq_appTop` records for the
restriction maps; for the inverse image no such identification is definitional, the sections of
an inverse image being a sheafified colimit. -/
theorem bijective_thickeningRingUnit_app (hZ : IsThickening B S hS X Z.1)
    (V : (SmallEtale B S hS X.1)ᵒᵖ) :
    Function.Bijective ((thickeningRingUnit B S hS Z).hom.app V) :=
  bijective_ringUnit_app_of_isThickening B S hS Z hZ (structureRingSheaf B S hS X) V

/-- **The direct image along any morphism of the unit of a thickening is an isomorphism.**  A
functor carries an isomorphism to an isomorphism, and the unit is one by
`AlgebraicGeometry.Space.isIso_thickeningRingUnit`.

This is what makes the sheaf of rings `(i ≫ c)_*(i^{-1}𝒪_X)` in which the comorphisms of the
morphisms agreeing on a thickening are compared — the target of
`AlgebraicGeometry.Space.structureSharpThroughThickening` — comparable with the direct image
`c_*𝒪_X`, whose sections over a chart the development reads by
`AlgebraicGeometry.Space.chartProjection`. -/
theorem isIso_map_thickeningRingUnit {W : AlgebraicSpaces B S hS} (c : X ⟶ W)
    (hZ : IsThickening B S hS X Z.1) :
    IsIso ((pushforwardRingFunctor (smallToposMorphismTypeU B S hS c)).map
      (thickeningRingUnit B S hS Z)) :=
  let := isIso_thickeningRingUnit B S hS Z hZ
  inferInstance

/-- **The direct image along any morphism of the unit of a thickening is bijective on the
sections over every étale chart of the target.** -/
theorem bijective_map_thickeningRingUnit_app {W : AlgebraicSpaces B S hS} (c : X ⟶ W)
    (hZ : IsThickening B S hS X Z.1) (V : (SmallEtale B S hS W.1)ᵒᵖ) :
    Function.Bijective (((pushforwardRingFunctor (smallToposMorphismTypeU B S hS c)).map
      (thickeningRingUnit B S hS Z)).hom.app V) :=
  let := isIso_map_thickeningRingUnit B S hS Z c hZ
  bijective_app_of_isIso _ V

/-! ### The two forms of the structure map through the identification -/

/-- **The two forms of the structure map of [Stacks Project, Tag 03G8] agree through the
identification of a sheaf of rings with the direct image of its inverse image**, read at a
section: the direct image of the inverse-image form `i^♯ : i^{-1}𝒪_X ⟶ 𝒪_Z`, applied to the
image of a regular function under the unit, is the direct-image form `i^♯ : 𝒪_X ⟶ i_*𝒪_Z`
applied to that function.

This is `AlgebraicGeometry.Space.ringUnit_comp_map_structureSharpRingInverseImage` on the
sections over one object of the site. -/
theorem app_ringUnit_comp_map_structureSharpRingInverseImage
    (V : (SmallEtale B S hS X.1)ᵒᵖ)
    (x : ToType ((structureRingSheaf B S hS X).obj.obj V)) :
    ((pushforwardRingFunctor (smallToposMorphismTypeU B S hS
          (subspaceInclusion B S hS X Z))).map
        (structureSharpRingInverseImage B S hS (subspaceInclusion B S hS X Z))).hom.app V
        ((ringUnit (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z))
          (structureRingSheaf B S hS X)).hom.app V x) =
      (structureSharp B S hS (subspaceInclusion B S hS X Z)).hom.app V x := by
  change (ringUnit (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z))
        (structureRingSheaf B S hS X) ≫
      (pushforwardRingFunctor (smallToposMorphismTypeU B S hS
          (subspaceInclusion B S hS X Z))).map
        (structureSharpRingInverseImage B S hS
          (subspaceInclusion B S hS X Z))).hom.app V x = _
  exact ringSheafHom_congr_app_apply
    (ringUnit_comp_map_structureSharpRingInverseImage B S hS
      (subspaceInclusion B S hS X Z)) V x

/-- **A regular function on an étale chart of `X` is killed by the inverse-image form of the
structure map, through the identification of the unit, exactly when it lies in the defining
ideal of the thickening at that chart.**  The two forms of the structure map agree through the
identification, and the defining ideal is by definition the kernel of the direct-image form. -/
theorem app_structureSharpRingInverseImage_ringUnit_app_eq_zero_iff
    (V : (SmallEtale B S hS X.1)ᵒᵖ)
    (x : ToType ((structureRingSheaf B S hS X).obj.obj V)) :
    ((pushforwardRingFunctor (smallToposMorphismTypeU B S hS
          (subspaceInclusion B S hS X Z))).map
        (structureSharpRingInverseImage B S hS (subspaceInclusion B S hS X Z))).hom.app V
        ((ringUnit (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z))
          (structureRingSheaf B S hS X)).hom.app V x) = 0 ↔
      x ∈ definingIdealAt B S hS X Z V := by
  rw [app_ringUnit_comp_map_structureSharpRingInverseImage B S hS Z V x]
  exact Iff.symm RingHom.mem_ker

/-- **The comparison of the inverse-image structure sheaf with the global sections of the
chart.**  For an étale scheme chart `V` of `X`, a regular function on `V` is killed by the
inverse-image form `i^♯ : i^{-1}𝒪_X ⟶ 𝒪_Z` of the structure map, read through the identification
of `Γ(V, ⊤)` with the sections of `i^{-1}𝒪_X` over the chart of `Z` lying under `V`, exactly
when it is killed by pullback of regular functions along the closed immersion of schemes
`Z ×_X V ⟶ V`.

Together with
`AlgebraicGeometry.Space.mem_range_firstOrderConormalModuleι_app_iff_appTop_eq_zero` this
identifies the sections of the conormal module of a first-order thickening over `V` with the
module `Stacks.Thickenings.conormalModuleAlong` of the scheme-level deformation theory. -/
theorem app_structureSharpRingInverseImage_ringUnit_app_eq_zero_iff_appTop
    (V : SmallEtale B S hS X.1)
    (x : ToType ((structureRingSheaf B S hS X).obj.obj (op V))) :
    ((pushforwardRingFunctor (smallToposMorphismTypeU B S hS
          (subspaceInclusion B S hS X Z))).map
        (structureSharpRingInverseImage B S hS (subspaceInclusion B S hS X Z))).hom.app (op V)
        ((ringUnit (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z))
          (structureRingSheaf B S hS X)).hom.app (op V) x) = 0 ↔
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
        (Z.2.2.rep.snd V.1.hom)).op).hom x = 0 := by
  refine (app_structureSharpRingInverseImage_ringUnit_app_eq_zero_iff B S hS Z (op V) x).trans ?_
  rw [definingIdealAt_eq_ker B S hS X Z V]
  exact RingHom.mem_ker

/-- **A section of the conormal module of a first-order thickening has, on an étale scheme chart
of `X`, a value killed by the inverse-image form of the structure map.**  Its value lies in the
defining ideal of the thickening at that chart, by
`AlgebraicGeometry.Space.range_firstOrderConormalModuleι_app`. -/
theorem app_structureSharpRingInverseImage_ringUnit_app_firstOrderConormalModuleι_app
    (hZ : IsFirstOrderThickening B S hS X Z.1) (V : (SmallEtale B S hS X.1)ᵒᵖ)
    (c : ((modulePullback B S hS (subspaceInclusion B S hS X Z) ⋙
        modulePushforward B S hS (subspaceInclusion B S hS X Z)).obj
      (definingIdealSheaf B S hS X Z).toSheafOfModules).val.obj V) :
    ((pushforwardRingFunctor (smallToposMorphismTypeU B S hS
          (subspaceInclusion B S hS X Z))).map
        (structureSharpRingInverseImage B S hS (subspaceInclusion B S hS X Z))).hom.app V
        ((ringUnit (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z))
            (structureRingSheaf B S hS X)).hom.app V
          ((firstOrderConormalModuleι B S hS Z hZ).val.app V c)) = 0 :=
  (app_structureSharpRingInverseImage_ringUnit_app_eq_zero_iff B S hS Z V _).2
    ((mem_range_firstOrderConormalModuleι_app_iff B S hS Z hZ V _).1 ⟨c, rfl⟩)

end AlgebraicGeometry.Space

end
