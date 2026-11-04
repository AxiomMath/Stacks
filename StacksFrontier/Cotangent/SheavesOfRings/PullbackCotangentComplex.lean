module

public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.RingedToposHomModules
public import StacksFrontier.Cotangent.SheavesOfRings.FundamentalTriangle
public import StacksFrontier.Cotangent.SheavesOfRings.InverseImageCotangentComplex

/-!
# The pullback of a cotangent complex along a morphism of ringed topoi

Let `φ : (Sh(C), 𝒪_C) ⟶ (Sh(D), 𝒪_D)` be a morphism of ringed topoi and let `a : A ⟶ 𝒪_D` be a
homomorphism of sheaves of commutative rings on `D`. The pullback `φ^*` of sheaves of modules is
the inverse image `φ⁻¹` followed by extension of scalars along `φ♯ : φ⁻¹𝒪_D ⟶ 𝒪_C`. Applied
degreewise to the cotangent complex `L_{𝒪_D/A}` it computes the degreewise base change
`L_{φ⁻¹𝒪_D/φ⁻¹A} ⊗_{φ⁻¹𝒪_D} 𝒪_C`, which is the first vertex of the fundamental triangle of the
tower `φ⁻¹A ⟶ φ⁻¹𝒪_D ⟶ 𝒪_C`.

## Main definitions

* `CategoryTheory.Sheaf.towerExtendScalarsCotangentComplexIso`: extending the scalars of the
  cotangent complex of `g : A ⟶ B` degreewise along `h : B ⟶ D` is the complex
  `CategoryTheory.Sheaf.baseChangedCotangentComplex` `L_{B/A} ⊗_B D`.
* `CategoryTheory.Sheaf.pullbackModulesCotangentComplexIso`: the degreewise pullback of
  `L_{𝒪_D/A}` along a morphism of ringed topoi is the first vertex of the fundamental triangle
  of `φ⁻¹A ⟶ φ⁻¹𝒪_D ⟶ 𝒪_C`.

## References

* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 08SV](https://stacks.math.columbia.edu/tag/08SV)
* [Stacks Project, Tag 08SZ](https://stacks.math.columbia.edu/tag/08SZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

universe u v w u' v' w'

namespace CategoryTheory.Sheaf

section Tower

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {A B D : Sheaf J CommRingCat.{max u v w}} (g : A ⟶ B) (h : B ⟶ D)

/-- Extension of scalars of sheaves of modules along `h : B ⟶ D` is additive. -/
instance additive_towerExtendScalars : (towerExtendScalars.{u, v, w} J h).Additive :=
  (towerExtendRestrictAdjunction.{u, v, w} J h).left_adjoint_additive

/-- Extending the scalars of the cotangent complex `L_{B/A}` degreewise along `h : B ⟶ D` gives
the complex `L_{B/A} ⊗_B D`. -/
noncomputable def towerExtendScalarsCotangentComplexIso :
    ((towerExtendScalars.{u, v, w} J h).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (cotangentComplex.{u, v, w} J g) ≅
      baseChangedCotangentComplex.{u, v, w} J g h :=
  (HomologicalComplex.mapHomologicalComplexExtendIso (towerExtendScalars.{u, v, w} J h)
      ((alternatingFaceMapComplex (targetModules.{u, v, w} J B)).obj
        (cotangentSimplicialModule.{u, v, w} J g).object)
      (ComplexShape.embeddingUpIntLE 0)).symm ≪≫
    ((ComplexShape.embeddingUpIntLE (0 : ℤ)).extendFunctor
        (targetModules.{u, v, w} J D)).mapIso
      ((alternatingFaceMapComplexCompMapHomologicalComplexIso
          (towerExtendScalars.{u, v, w} J h)).app
        (cotangentSimplicialModule.{u, v, w} J g).object)

end Tower

section RingedTopos

open AlgebraicGeometry

variable {X : RingedTopos.{v, u, max u v w}} {Y : RingedTopos.{v', u', max u' v' w'}}
  [X.J.HasSheafCompose (forget RingCat.{max u v w})]
  [Y.J.HasSheafCompose (forget RingCat.{max u' v' w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{max u' v' w'} RingCat.{max u' v' w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{max u v w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  (φ : RingedToposHom X Y)

/-- The pullback of sheaves of modules along a morphism of ringed topoi is additive. -/
instance additive_toRingedToposModulesHom_pullbackModules :
    (φ.toRingedToposModulesHom.pullbackModules).Additive := by
  have h₁ := inverseImageTargetModules_additive.{u, v, w, u', v', w'} X.J Y.J φ.toToposHom
    (B := Y.O)
  have h₂ := additive_towerExtendScalars.{u, v, w} X.J φ.fSharpInverseImage
  exact ⟨fun {_ _ f g} ↦ (congrArg (towerExtendScalars.{u, v, w} X.J φ.fSharpInverseImage).map
    (h₁.map_add (f := f) (g := g))).trans h₂.map_add⟩

/-- For a morphism of ringed topoi `φ : (Sh(C), 𝒪_C) ⟶ (Sh(D), 𝒪_D)` and a homomorphism
`a : A ⟶ 𝒪_D` of sheaves of commutative rings on `D`, the degreewise pullback `φ^*L_{𝒪_D/A}` is
the degreewise base change `L_{φ⁻¹𝒪_D/φ⁻¹A} ⊗_{φ⁻¹𝒪_D} 𝒪_C` along `φ♯ : φ⁻¹𝒪_D ⟶ 𝒪_C`. -/
noncomputable def pullbackModulesCotangentComplexIso {A : Sheaf Y.J CommRingCat.{max u' v' w'}}
    (a : A ⟶ Y.O) :
    ((φ.toRingedToposModulesHom.pullbackModules).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (cotangentComplex.{u', v', w'} Y.J a) ≅
      baseChangedCotangentComplex.{u, v, w} X.J (φ.toToposHom.inverseImageRing.map a)
        φ.fSharpInverseImage :=
  letI : (towerExtendScalars.{u, v, w} X.J (B := φ.toToposHom.inverseImageRing.obj Y.O)
      φ.fSharpInverseImage).Additive :=
    additive_towerExtendScalars.{u, v, w} X.J φ.fSharpInverseImage
  ((Functor.mapHomologicalComplexCompIso
      (F := inverseImageTargetModules.{u, v, w, u', v', w'} X.J Y.J φ.toToposHom (B := Y.O))
      (G := towerExtendScalars.{u, v, w} X.J φ.fSharpInverseImage)
      (H := φ.toRingedToposModulesHom.pullbackModules) (Iso.refl _)
      (ComplexShape.up ℤ)).app (cotangentComplex.{u', v', w'} Y.J a)).symm ≪≫
    ((towerExtendScalars.{u, v, w} X.J φ.fSharpInverseImage).mapHomologicalComplex
        (ComplexShape.up ℤ)).mapIso
      (inverseImageCotangentComplexIso.{u, v, w, u', v', w'} X.J Y.J φ.toToposHom a) ≪≫
    towerExtendScalarsCotangentComplexIso.{u, v, w} X.J _ _

end RingedTopos

end CategoryTheory.Sheaf

end
