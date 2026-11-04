module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.IdealSheafPowers
public import StacksFrontier.AlgebraicGeometry.Spaces.MorphismKernelIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardStructureSheafIntegral
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedClosedSubspaceIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStructureMapComp

/-!
# Precomposition and the kernel ideal sheaf of a morphism of algebraic spaces

Let `S` be a scheme contained in a big fppf site `B`.  To a morphism `f : X ⟶ Y` of algebraic
spaces over `S` the structure map `f♯ : 𝒪_Y ⟶ f_*𝒪_X` of Stacks 03G8 attaches a sheaf of ideals
of `𝒪_Y`, the kernel `AlgebraicGeometry.Space.kernelIdealSheaf` of that map on every étale scheme
chart of `Y`.  This file records how it responds to precomposition:

* it only grows — `kernelIdealSheaf g ≤ kernelIdealSheaf (f ≫ g)` for an arbitrary `f`; and so
* it is unchanged by precomposition with an **isomorphism**.

For the inclusion of a closed subspace the kernel ideal sheaf is the defining ideal sheaf of
Stacks 03MB (`AlgebraicGeometry.Space.kernelIdealSheaf_eq_definingIdealSheaf`), so the defining
ideal sheaf of a closed subspace is also the kernel ideal sheaf of the inclusion composed with any
isomorphism of the source. In particular, for a closed subscheme of a scheme of the site, the
defining ideal sheaf of its range is the kernel ideal sheaf of the *represented* morphism.

## Main results

* `AlgebraicGeometry.Space.ker_structureSharp_le_comp`: the kernel of the structure map on sections
  over an étale chart only grows under precomposition, with no hypothesis on the morphism
  precomposed.
* `AlgebraicGeometry.Space.kernelIdealSheaf_le_precomp`: the same as an inclusion of sheaves of
  ideals.
* `AlgebraicGeometry.Space.kernelIdealSheaf_iso_comp`: **the kernel ideal sheaf is invariant under
  precomposition with an isomorphism.**
* `AlgebraicGeometry.Space.kernelIdealSheaf_representedSpaceMap`: the kernel ideal sheaf of the
  morphism of algebraic spaces represented by a closed immersion `j` of the site is the defining
  ideal sheaf of `AlgebraicGeometry.Space.closedSubspaceRange`, the range of `j` read as a closed
  subspace.
* `AlgebraicGeometry.Space.definingIdealAt_closedSubspaceRange`: the same read on sections over an
  étale scheme chart, where it is a kernel of a map of rings of global sections of schemes.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace CategoryTheory.Sheaf

variable {C : Type*} [Category C] {J : GrothendieckTopology C}

/-- A section killed by a morphism of sheaves of commutative rings is killed by any composite
beginning with it. -/
theorem apply_comp_app_eq_zero {A A' A'' : Sheaf J CommRingCat.{u}} (α : A ⟶ A') (β : A' ⟶ A'')
    (U : Cᵒᵖ) (a : ToType (A.obj.obj U)) (ha : (α.hom.app U).hom a = 0) :
    ((α ≫ β).hom.app U).hom a = 0 := by
  have h : (α ≫ β).hom.app U = α.hom.app U ≫ β.hom.app U := rfl
  rw [h, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, ha, map_zero]

end CategoryTheory.Sheaf

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Comp

variable {X Y Z : AlgebraicSpaces B S hS}

/-- **The structure map of a composite kills whatever the second factor kills.**  A regular
function on an étale scheme chart of `Z` killed by `g♯ : 𝒪_Z ⟶ g_*𝒪_Y` is killed by
`(f ≫ g)♯ : 𝒪_Z ⟶ (f ≫ g)_*𝒪_X`, for an arbitrary `f : X ⟶ Y`. -/
theorem structureSharp_comp_app_apply_eq_zero (f : X ⟶ Y) (g : Y ⟶ Z)
    (U : (SmallEtale B S hS Z.1)ᵒᵖ) (a : ToType ((structureRingSheaf B S hS Z).obj.obj U))
    (ha : ((structureSharp B S hS g).hom.app U).hom a = 0) :
    ((structureSharp B S hS (f ≫ g)).hom.app U).hom a = 0 := by
  have hzero : ((smallEtaleRingedToposHom B S hS g).fSharp.hom.app U).hom a = 0 :=
    (fSharp_app_apply B S hS g U a).trans ha
  obtain ⟨rest, hrest⟩ : ∃ r, ((smallEtaleRingedToposHom B S hS g).comp
      (smallEtaleRingedToposHom B S hS f)).fSharp =
      (smallEtaleRingedToposHom B S hS g).fSharp ≫ r := ⟨_, rfl⟩
  refine Eq.trans (fSharp_app_apply B S hS (f ≫ g) U a).symm ?_
  rw [← smallEtaleRingedToposHom_comp_fSharp B S hS f g, hrest, Category.assoc]
  exact Sheaf.apply_comp_app_eq_zero _ _ U a hzero

/-- **Precomposition only grows the kernel of the structure map.**  On sections over an étale
scheme chart of `Z` the kernel of `g♯` is contained in the kernel of `(f ≫ g)♯`, for an arbitrary
`f`. -/
theorem ker_structureSharp_le_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (U : (SmallEtale B S hS Z.1)ᵒᵖ) :
    RingHom.ker ((structureSharp B S hS g).hom.app U).hom ≤
      RingHom.ker ((structureSharp B S hS (f ≫ g)).hom.app U).hom := fun _ ha =>
  RingHom.mem_ker.2 (structureSharp_comp_app_apply_eq_zero B S hS f g U _ (RingHom.mem_ker.1 ha))

/-- **Precomposition with an isomorphism does not change the kernel of the structure map.** On
sections over an étale scheme chart of `Z` the kernel of `(e.hom ≫ f)♯` is the kernel of `f♯`. -/
theorem ker_structureSharp_iso_comp (e : X ≅ Y) (f : Y ⟶ Z)
    (U : (SmallEtale B S hS Z.1)ᵒᵖ) :
    RingHom.ker ((structureSharp B S hS (e.hom ≫ f)).hom.app U).hom =
      RingHom.ker ((structureSharp B S hS f).hom.app U).hom := by
  refine le_antisymm ?_ (ker_structureSharp_le_comp B S hS e.hom f U)
  have h := ker_structureSharp_le_comp B S hS e.inv (e.hom ≫ f) U
  rwa [Iso.inv_hom_id_assoc] at h

/-- **Precomposition only grows the kernel ideal sheaf**, as an inclusion of sheaves of ideals of
`𝒪_Z`. -/
theorem kernelIdealSheaf_le_precomp (f : X ⟶ Y) (g : Y ⟶ Z) :
    kernelIdealSheaf B S hS g ≤ kernelIdealSheaf B S hS (f ≫ g) :=
  SheafOfModules.idealSheaf_le fun U => ker_structureSharp_le_comp B S hS f g U

/-- **The kernel ideal sheaf is invariant under precomposition with an isomorphism.** -/
theorem kernelIdealSheaf_iso_comp (e : X ≅ Y) (f : Y ⟶ Z) :
    kernelIdealSheaf B S hS (e.hom ≫ f) = kernelIdealSheaf B S hS f :=
  SheafOfModules.idealSheaf_ext fun U => ker_structureSharp_iso_comp B S hS e f U

end Comp

section Represented

variable {R V : BigFppfOver B S hS}

/-- **The kernel ideal sheaf of a represented closed immersion is the defining ideal sheaf of its
range.**  For a morphism `j : R ⟶ V` of the big fppf category over `S` whose underlying morphism
of schemes is a closed immersion, the kernel of the structure map of the represented morphism of
algebraic spaces `yoneda.obj R ⟶ yoneda.obj V` is the sheaf of ideals of Stacks 03MB of the closed
subspace `AlgebraicGeometry.Space.closedSubspaceRange`. -/
theorem kernelIdealSheaf_representedSpaceMap (j : R ⟶ V)
    (hj : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j)) :
    kernelIdealSheaf B S hS (representedSpaceMap B S hS j) =
      definingIdealSheaf B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
        (closedSubspaceRange B S hS j hj) :=
  (congrArg (fun m : (⟨yoneda.obj R, isAlgebraicSpace_yoneda B S hS R⟩ :
        AlgebraicSpaces B S hS) ⟶ ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ =>
      kernelIdealSheaf B S hS m)
    (rangeSpaceIso_hom_comp_subspaceInclusion B S hS j hj).symm).trans
    ((kernelIdealSheaf_iso_comp B S hS (rangeSpaceIso B S hS j hj)
        (subspaceInclusion B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
          (closedSubspaceRange B S hS j hj))).trans
      (kernelIdealSheaf_eq_definingIdealSheaf B S hS
        ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
        (closedSubspaceRange B S hS j hj)))

/-- **The defining ideal of the range of a closed immersion of the site, on an étale scheme
chart.**  It is the kernel of the structure map of the represented morphism on sections over that
chart, and hence a kernel of a homomorphism of rings of global sections of schemes. -/
theorem definingIdealAt_closedSubspaceRange (j : R ⟶ V)
    (hj : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j))
    (U : SmallEtale B S hS (yoneda.obj V)) :
    definingIdealAt B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
        (closedSubspaceRange B S hS j hj) (op U) =
      RingHom.ker (chartPullbackRingHom B S hS (representedSpaceMap B S hS j) U
        (chartBaseChangeArrow B S hS (representedSpaceMap B S hS j)
          (relativelyRepresentable_yoneda_map B S hS j) U)) :=
  (congrArg (fun N : (SheafOfModules.unit
      (structureRingSheaf B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩)).Submodule =>
        N.obj (op U)) (kernelIdealSheaf_representedSpaceMap B S hS j hj)).symm.trans
    (ker_structureSharp_eq B S hS (representedSpaceMap B S hS j)
      (relativelyRepresentable_yoneda_map B S hS j) U)

end Represented

end AlgebraicGeometry.Space

end
