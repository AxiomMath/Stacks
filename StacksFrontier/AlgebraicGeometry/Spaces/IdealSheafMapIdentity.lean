module

public import StacksFrontier.AlgebraicGeometry.Spaces.IdealSheafMapKernel
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealSheafMapVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsIdComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureProjectionComposition

/-!
# The map of defining ideal sheaves of a chain of closed subspaces is the inclusion

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B` and let
`Z ⊆ Y ⊆ X` be closed subspaces.  The map `g^*𝓘_Y ⟶ 𝓘_Z` of [Stacks Project, Tag 04CP] attached to
the commutative square with lower edge `g` is, at `g = 𝟙_X`, the inclusion `𝓘_Y ⊆ 𝓘_Z` of
`AlgebraicGeometry.Space.definingIdealSheafHomOfLe` read through the unit law `(𝟙_X)^* ≅ 𝟭` of
[Stacks Project, Tag 03LU].  Consequently the left-hand map `ι^*𝒞_{Y/X} ⟶ 𝒞_{Z/X}` of the conormal
complex of the chain — the map of [Stacks Project, Tag 04CP] at the square of
`AlgebraicGeometry.Space.subspaceInclusion_homOfLe_square` — is the inverse image along the
inclusion `i : Z ⟶ X` of that inclusion of ideal sheaves, up to an isomorphism of its source.

The missing link was the behaviour of the canonical comparison `g^*𝒪_X ⟶ 𝒪_X` of
`AlgebraicGeometry.Space.structureModulePullbackMap` at an identity, and that is the first half of
this file.

## Main results

* `AlgebraicGeometry.Space.structureProjectionOfHom_id_eq`: the canonical morphism
  `𝒪_X ⟶ (𝟙_X)_*𝒪_X` of [Stacks Project, Tag 03G8] is the inverse of the unit law
  `(𝟙_X)_* ≅ 𝟭` for the direct image of modules.
* `AlgebraicGeometry.Space.structureModulePullbackMap_id`: the canonical comparison
  `(𝟙_X)^*𝒪_X ⟶ 𝒪_X` is the unit law `AlgebraicGeometry.Space.modulePullbackIdIso` of
  [Stacks Project, Tag 03LU] at the structure sheaf.
* `AlgebraicGeometry.Space.idealSheafMap_id_eq`: **the map of defining ideal sheaves at an
  identity is the inclusion.**  For `Z ⊆ Y` the map `(𝟙_X)^*𝓘_Y ⟶ 𝓘_Z` of [Stacks Project,
  Tag 04CP] is the unit law at `𝓘_Y` followed by
  `AlgebraicGeometry.Space.definingIdealSheafHomOfLe`.
* `AlgebraicGeometry.Space.exists_iso_comp_eq_conormalMap_homOfLe`: **the left-hand map of the
  conormal complex of the chain is the inverse image of that inclusion**, up to an isomorphism of
  its source.

## Implementation notes

**Both halves are proved by transposing.**  The canonical morphism `𝒪_X ⟶ f_*𝒪_X` of modules and
the canonical comparison `f^*𝒪_X ⟶ 𝒪_X` are transposes of each other along the adjunction of
[Stacks Project, Tag 03D7], by
`AlgebraicGeometry.Space.structureProjectionOfHom_eq_homEquiv_structureModulePullbackMap`, and the
transpose of the unit law for the inverse image is the inverse of the unit law for the direct
image, by `AlgebraicGeometry.Space.homEquiv_modulePullbackIdIso_hom_app`.  So the comparison at an
identity is pinned by a statement about direct images, and that one is checked on underlying
sheaves of sets: the structure map of an identity is the canonical identification of the direct
image along an identity with the identity functor
(`AlgebraicGeometry.Space.structureSharpSet_id`), which is exactly what the unit law for the
direct image of modules is built from
(`AlgebraicGeometry.Space.moduleSheafFunctor_map_modulePushforwardIdIso_inv_app`).

**The identification of the ideal-sheaf map is made after the inclusion into `𝒪_X`.**  That
inclusion is a monomorphism, so the two maps `(𝟙_X)^*𝓘_Y ⟶ 𝓘_Z` agree as soon as they agree after
it, where `AlgebraicGeometry.Space.idealSheafMap_comp_definingIdealSheaf_ι` turns the left-hand
one into the inverse image of `𝓘_Y ⊆ 𝒪_X` read in `𝒪_X` and
`AlgebraicGeometry.Space.definingIdealSheafHomOfLe_comp_ι` turns the right-hand one into the unit
law followed by `𝓘_Y ⊆ 𝒪_X`.  Naturality of the unit law at `𝓘_Y ⊆ 𝒪_X` closes the gap.

**The proofs are in term mode.**  A goal whose two ends are spelled one as an
`AlgebraicGeometry.Space.Modules` and the other as a `SheafOfModules` over the structure ring
sheaf is not type-correct at `implicit` transparency, so the rewriting tactics cannot be used on
it; this is the device the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/IdealSheafMapKernel.lean` describe, and the chains below
are built from `Eq.trans` and `congrArg` for the same reason.

**No `@[stacks]` attribute is placed.**  [Stacks Project, Tag 04CP] produces the map and
[Stacks Project, Tag 03LU] the unit law; neither says anything about the value of the first at an
identity, and neither does [Stacks Project, Tag 03MB] about the inclusion of defining ideal
sheaves.  The statements below are the plumbing that the proof of [Stacks Project, Tag 06D8]
needs, not clauses of a tag.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 06D8](https://stacks.math.columbia.edu/tag/06D8)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The canonical comparison of structure sheaves at an identity -/

/-- **The canonical morphism `𝒪_X ⟶ (𝟙_X)_*𝒪_X` of [Stacks Project, Tag 03G8] is the unit law for
the direct image of modules, inverted.**  On underlying sheaves of sets the first is the structure
map of the identity (`AlgebraicGeometry.Space.moduleSheafFunctor_map_structureProjectionOfHom`),
which is the canonical identification of the direct image of sheaves of sets along an identity
with the identity functor (`AlgebraicGeometry.Space.structureSharpSet_id`), and that
identification is what the unit law for the direct image of modules is
(`AlgebraicGeometry.Space.moduleSheafFunctor_map_modulePushforwardIdIso_inv_app`).  A morphism of
sheaves of modules is determined by its underlying morphism of sheaves of sets. -/
theorem structureProjectionOfHom_id_eq (X : AlgebraicSpaces B S hS) :
    structureProjectionOfHom B S hS (𝟙 X) =
      (modulePushforwardIdIso B S hS X).inv.app
        (SheafOfModules.unit (structureRingSheaf B S hS X)) :=
  Stacks.Sheaves.RingedToposModules.hom_ext_moduleSheafFunctor
    (R := structureRingSheaf B S hS X)
    ((moduleSheafFunctor_map_structureProjectionOfHom B S hS (𝟙 X)).trans
      ((structureSharpSet_id B S hS X).trans
        (moduleSheafFunctor_map_modulePushforwardIdIso_inv_app B S hS X
          (SheafOfModules.unit (structureRingSheaf B S hS X))).symm))

/-- **The canonical comparison `(𝟙_X)^*𝒪_X ⟶ 𝒪_X` is the unit law `(𝟙_X)^* ≅ 𝟭` of
[Stacks Project, Tag 03LU] at the structure sheaf.**

The two sides have the same transpose along the adjunction of [Stacks Project, Tag 03D7]: on the
left it is the canonical morphism `𝒪_X ⟶ (𝟙_X)_*𝒪_X` by
`AlgebraicGeometry.Space.structureProjectionOfHom_eq_homEquiv_structureModulePullbackMap`, on the
right the inverse of the unit law for the direct image by
`AlgebraicGeometry.Space.homEquiv_modulePullbackIdIso_hom_app`, and those agree by
`AlgebraicGeometry.Space.structureProjectionOfHom_id_eq`. -/
theorem structureModulePullbackMap_id (X : AlgebraicSpaces B S hS) :
    structureModulePullbackMap B S hS (𝟙 X) =
      (modulePullbackIdIso B S hS X).hom.app
        (SheafOfModules.unit (structureRingSheaf B S hS X)) :=
  ((modulePullbackAdjunction B S hS (𝟙 X)).homEquiv _ _).injective
    (((structureProjectionOfHom_eq_homEquiv_structureModulePullbackMap B S hS (𝟙 X)).symm.trans
      (structureProjectionOfHom_id_eq B S hS X)).trans
      (homEquiv_modulePullbackIdIso_hom_app B S hS X
        (SheafOfModules.unit (structureRingSheaf B S hS X))).symm)

/-! ### The map of defining ideal sheaves of a chain -/

variable {X : AlgebraicSpaces B S hS} (Y Z : ClosedSubspaces B S hS X.1) (hZY : Z.1 ≤ Y.1)

/-- **The map of defining ideal sheaves at an identity is the inclusion.**  For closed subspaces
`Z ⊆ Y ⊆ X` the map `(𝟙_X)^*𝓘_Y ⟶ 𝓘_Z` of [Stacks Project, Tag 04CP] attached to the square of
`AlgebraicGeometry.Space.subspaceInclusion_homOfLe_square` is the unit law
`AlgebraicGeometry.Space.modulePullbackIdIso` of [Stacks Project, Tag 03LU] at `𝓘_Y`, followed by
the inclusion `𝓘_Y ⊆ 𝓘_Z` of `AlgebraicGeometry.Space.definingIdealSheafHomOfLe`.

The inclusion `𝓘_Z ⊆ 𝒪_X` is a monomorphism, so it is enough to check this after it, where
`AlgebraicGeometry.Space.idealSheafMap_comp_definingIdealSheaf_ι` and
`AlgebraicGeometry.Space.structureModulePullbackMap_id` turn the left-hand side into the inverse
image of `𝓘_Y ⊆ 𝒪_X` followed by the unit law at `𝒪_X`, which naturality moves past the inclusion,
and `AlgebraicGeometry.Space.definingIdealSheafHomOfLe_comp_ι` turns the right-hand side into the
unit law at `𝓘_Y` followed by `𝓘_Y ⊆ 𝒪_X`. -/
theorem idealSheafMap_id_eq :
    idealSheafMap B S hS Z Y (𝟙 X) (ObjectProperty.homMk (Subfunctor.homOfLe hZY))
        (subspaceInclusion_homOfLe_square B S hS Y Z hZY) =
      (modulePullbackIdIso B S hS X).hom.app
          (definingIdealSheaf B S hS X Y).toSheafOfModules ≫
        definingIdealSheafHomOfLe B S hS Y Z hZY := by
  refine (cancel_mono (definingIdealSheaf B S hS X Z).ι).mp ?_
  refine Eq.trans (idealSheafMap_comp_definingIdealSheaf_ι B S hS Z Y (𝟙 X)
      (ObjectProperty.homMk (Subfunctor.homOfLe hZY))
      (subspaceInclusion_homOfLe_square B S hS Y Z hZY)) ?_
  refine Eq.trans (congrArg (fun m ↦ (modulePullback B S hS (𝟙 X)).map
      (definingIdealSheaf B S hS X Y).ι ≫ m) (structureModulePullbackMap_id B S hS X)) ?_
  refine Eq.trans ((modulePullbackIdIso B S hS X).hom.naturality
      (definingIdealSheaf B S hS X Y).ι) ?_
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  exact congrArg (fun m ↦ (modulePullbackIdIso B S hS X).hom.app
      (definingIdealSheaf B S hS X Y).toSheafOfModules ≫ m)
    (definingIdealSheafHomOfLe_comp_ι B S hS Y Z hZY).symm

/-- **The left-hand map of the conormal complex of a chain of closed subspaces is the inverse
image of the inclusion of defining ideal sheaves.**  For `Z ⊆ Y ⊆ X` the map
`ι^*𝒞_{Y/X} ⟶ 𝒞_{Z/X}` of [Stacks Project, Tag 04CP] at the square of
`AlgebraicGeometry.Space.subspaceInclusion_homOfLe_square` is the inverse image along the inclusion
`i : Z ⟶ X` of `AlgebraicGeometry.Space.definingIdealSheafHomOfLe`, precomposed with an
isomorphism `ι^*𝒞_{Y/X} ≅ i^*𝓘_Y`.

The isomorphism is the comparison factor
`AlgebraicGeometry.Space.conormalPullbackComparison` of the conormal map, which is invertible by
`AlgebraicGeometry.Space.isIso_conormalPullbackComparison`, followed by the inverse image along
`i` of the unit law at `𝓘_Y`; the equation is
`AlgebraicGeometry.Space.conormalMap_eq` together with
`AlgebraicGeometry.Space.idealSheafMap_id_eq`. -/
theorem exists_iso_comp_eq_conormalMap_homOfLe :
    ∃ ρ : (modulePullback B S hS
            (ObjectProperty.homMk (Subfunctor.homOfLe hZY) :
              (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
                (⟨Y.1.toFunctor, Y.2.1⟩ : AlgebraicSpaces B S hS))).obj
          (conormalModule B S hS X Y) ≅
        (modulePullback B S hS (subspaceInclusion B S hS X Z)).obj
          (definingIdealSheaf B S hS X Y).toSheafOfModules,
      ρ.hom ≫
          (show (modulePullback B S hS (subspaceInclusion B S hS X Z)).obj
                (definingIdealSheaf B S hS X Y).toSheafOfModules ⟶
              conormalModule B S hS X Z from
            (modulePullback B S hS (subspaceInclusion B S hS X Z)).map
              (definingIdealSheafHomOfLe B S hS Y Z hZY)) =
        conormalMap B S hS Z Y (𝟙 X) (ObjectProperty.homMk (Subfunctor.homOfLe hZY))
          (subspaceInclusion_homOfLe_square B S hS Y Z hZY) := by
  have := isIso_conormalPullbackComparison B S hS Z Y (𝟙 X)
    (ObjectProperty.homMk (Subfunctor.homOfLe hZY))
    (subspaceInclusion_homOfLe_square B S hS Y Z hZY)
  refine ⟨asIso (conormalPullbackComparison B S hS Z Y (𝟙 X)
      (ObjectProperty.homMk (Subfunctor.homOfLe hZY))
      (subspaceInclusion_homOfLe_square B S hS Y Z hZY)) ≪≫
    (modulePullback B S hS (subspaceInclusion B S hS X Z)).mapIso
      ((modulePullbackIdIso B S hS X).app
        (definingIdealSheaf B S hS X Y).toSheafOfModules), ?_⟩
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun m ↦ conormalPullbackComparison B S hS Z Y (𝟙 X)
      (ObjectProperty.homMk (Subfunctor.homOfLe hZY))
      (subspaceInclusion_homOfLe_square B S hS Y Z hZY) ≫ m)
    (((modulePullback B S hS (subspaceInclusion B S hS X Z)).map_comp
        ((modulePullbackIdIso B S hS X).hom.app
          (definingIdealSheaf B S hS X Y).toSheafOfModules)
        (definingIdealSheafHomOfLe B S hS Y Z hZY)).symm.trans
      (congrArg (modulePullback B S hS (subspaceInclusion B S hS X Z)).map
        (idealSheafMap_id_eq B S hS Y Z hZY).symm))) ?_
  exact (conormalMap_eq B S hS Z Y (𝟙 X) (ObjectProperty.homMk (Subfunctor.homOfLe hZY))
    (subspaceInclusion_homOfLe_square B S hS Y Z hZY)).symm

end AlgebraicGeometry.Space

end
