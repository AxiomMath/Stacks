module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposHomOfRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSmallEtaleMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSmallEtaleTopology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.RingedToposOfAMorphism
public import StacksFrontier.Deformation.ToposThickening.Trivialization.RingedToposComp

/-!
# The augmentation of a simplicial algebraic space as a morphism of ringed topoi

Let `X` be a simplicial algebraic space with an augmentation `a : X → X₋₁` (Stacks 0DE7). Viewing
`a` as a morphism `X ⟶ const(X₋₁)` of simplicial algebraic spaces, it is the composite of the
morphism of ringed topoi of base change along `a` of
`AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.ringedToposHom` with the morphism of ringed
topoi `ε : Sh(const(X₋₁)_{spaces,étale}) ⟶ Sh(X₋₁,spaces,étale)` of the functor forgetting the
simplicial degree, which is continuous and cocontinuous. The inverse image of `ε` is restriction
along that functor, so that `a⁻¹𝒢` has components `a_n⁻¹𝒢`, and the structure map of `ε` is the
identification `ε⁻¹𝒪_{X₋₁} = 𝒪_{const(X₋₁)}`.

## Main definitions

* `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.constForget`: the functor
  `const(Z)_{spaces,étale} ⥤ Z_{spaces,étale}`, `V/Z ↦ V/Z`.
* `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.constRingedToposHom`: the morphism of
  ringed topoi `ε` it defines.
* `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.augmentationRingedToposHom`: **the morphism
  of ringed topoi `a : (Sh(X_étale), 𝒪) ⟶ (Sh(X₋₁,étale), 𝒪_{X₋₁})` of an augmentation.**
-/

@[expose] public section

open CategoryTheory Opposite CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

variable (Z : AlgebraicSpaces B S hS)

/-- The functor `const(Z)_{spaces,étale} ⥤ Z_{spaces,étale}` forgetting the simplicial degree of
an object of the spaces-étale site of the constant simplicial algebraic space on `Z`. -/
@[simps]
def constForget :
    SimplicialSpacesEtaleSite B S hS ((Functor.const _).obj Z) ⥤ SpacesEtale B S hS Z where
  obj U := U.obj
  map f := ObjectProperty.homMk (Over.homMk f.hom (f.w.trans (Category.comp_id _)))
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Forgetting the degree of an object of a single degree is the identity. -/
theorem degreeInclusion_comp_constForget (n : SimplexCategory) :
    degreeInclusion ((Functor.const _).obj Z) n ⋙ constForget Z = 𝟭 _ := rfl

/-- Forgetting the simplicial degree is cocontinuous. -/
instance constForget_isCocontinuous :
    (constForget Z).IsCocontinuous (topology ((Functor.const _).obj Z))
      (SpacesEtale.topology B S hS Z) where
  cover_lift {U} {T} hT := by
    refine GrothendieckTopology.superset_covering _ ?_
      (functorPushforward_degreeInclusion_mem (X := (Functor.const _).obj Z) (n := U.degree)
        (V := U.obj) hT)
    rintro Y f ⟨W, g, k, hg, rfl⟩
    exact T.downward_closed hg ((constForget Z).map k)

/-- Forgetting the simplicial degree is continuous. -/
instance constForget_isContinuous :
    (constForget Z).IsContinuous (topology ((Functor.const _).obj Z))
      (SpacesEtale.topology B S hS Z) where
  op_comp_isSheaf_of_types G := by
    rw [Presieve.isSheaf_coverage]
    rintro U R ⟨E, hE, rfl⟩
    refine Presieve.isSheafFor_ofArrows_map_of_isSheafFor_simplicialSmallEtaleSite
      (degreeInclusion ((Functor.const _).obj Z) U.degree) _ E.X E.f ?_
    exact (Presieve.isSheafFor_iff_generate _).2 ((isSheaf_iff_isSheaf_of_type _ _).1 G.2 _
      (Precoverage.generate_mem_toGrothendieck
        ((SpacesEtale.mem_precoverage_iff B S hS Z).2 ⟨E, rfl, hE⟩)))

/-- The morphism of topoi `ε : Sh(const(Z)_{spaces,étale}) ⟶ Sh(Z_{spaces,étale})` of the
functor forgetting the simplicial degree: its inverse image is restriction. -/
noncomputable def constToposHom :
    MorphismOfTopoi (Sheaf (topology ((Functor.const _).obj Z)) (Type (u + 1)))
      (Sheaf (SpacesEtale.topology B S hS Z) (Type (u + 1))) :=
  Functor.morphismOfTopoiOfCocontinuous.{u + 1, u + 1, u + 1, u + 1, u + 1} (constForget Z) _ _

/-- The structure sheaf of `const(Z)` is the restriction of that of `Z`. -/
theorem structureSheaf_const :
    structureSheaf ((Functor.const _).obj Z) =
      ((constForget Z).sheafPushforwardContinuous CommRingCat.{u + 1}
        (topology ((Functor.const _).obj Z)) (SpacesEtale.topology B S hS Z)).obj
        (SpacesEtale.structureSheaf B S hS Z) := rfl

/-- **Stacks 0DE7.** The morphism of ringed topoi
`ε : (Sh(const(Z)_étale), 𝒪) ⟶ (Sh(Z_étale), 𝒪_Z)` forgetting the simplicial degree. -/
noncomputable def constRingedToposHom :
    RingedToposHom (ringedTopos ((Functor.const _).obj Z)) (spacesEtaleRingedTopos B S hS Z) :=
  RingedToposHom.ofInverseImageIso (X := ringedTopos ((Functor.const _).obj Z))
    (Y := spacesEtaleRingedTopos B S hS Z) (constToposHom Z)
    (Stacks.Sheaves.ToposPullback.restrictionCommRingIso (topology ((Functor.const _).obj Z))
      (SpacesEtale.topology B S hS Z) (constForget Z) (SpacesEtale.structureSheaf B S hS Z))

variable {Z} {X : SimplicialObject (AlgebraicSpaces B S hS)}

/-- **Stacks 0DE7.** The morphism of ringed topoi
`a : (Sh(X_étale), 𝒪) ⟶ (Sh(X₋₁,étale), 𝒪_{X₋₁})` of an augmentation `a : X → X₋₁` of a
simplicial algebraic space: base change along `a`, followed by forgetting the degree. Its inverse
image sends `𝒢` to the sheaf with components `a_n⁻¹𝒢`, and its structure map is given in degree
`n` by `a_n♯`. -/
noncomputable def augmentationRingedToposHom (a : X ⟶ (Functor.const _).obj Z) :
    RingedToposHom (ringedTopos X) (spacesEtaleRingedTopos B S hS Z) :=
  RingedToposHom.comp (X := ringedTopos X) (Y := ringedTopos ((Functor.const _).obj Z))
    (Z := spacesEtaleRingedTopos B S hS Z) (constRingedToposHom Z) (ringedToposHom a)

end AlgebraicGeometry.Space.SimplicialSpacesEtaleSite
