module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.PullbackSections
import all StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.PullbackSections
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.Functoriality
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.OpenImmersion

/-!
# The presheaf of relative differentials on schemes over a base

For a scheme `S`, the global sections of the sheaf of relative differentials of each scheme
over `S` form an abelian-group-valued presheaf on the category of schemes over `S`. Its
restriction maps are the maps on global sections adjoint to the canonical morphisms on relative
differentials of the squares with identity base edge.

## Main definitions

* `AlgebraicGeometry.differentialSectionsMap` is the canonical map on global sections of
  relative differentials induced by a morphism of schemes over `S`.
* `AlgebraicGeometry.RelativeDifferentialsPresheaf` records the presheaf together with its
  prescribed values on objects and morphisms.
* `AlgebraicGeometry.relativeDifferentialsPresheaf` is the presheaf of relative differentials
  of schemes over `S`.

## Implementation notes

The displayed objectwise formula in the source is represented by the isomorphisms in
`RelativeDifferentialsPresheaf.objIso`, and the field `map_objIso` pins the restriction maps
down to the canonical ones, so the structure is not merely an objectwise assignment.

The functor laws come from the corresponding identities for the adjoint morphism
`Ω_{Y/S} ⟶ g_* Ω_{X/S}`, which in turn come from the uniqueness part of the functoriality of
relative differentials: both the identity and the composition identity are checked by
exhibiting the relevant morphism as a map of relative differentials.

## References

* [Stacks Project, Tag 01UV](https://stacks.math.columbia.edu/tag/01UV)
* [Stacks Project, Tag 08RM](https://stacks.math.columbia.edu/tag/08RM)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

attribute [local simp] Scheme.Modules.pseudofunctor_associativity
  Scheme.Modules.pseudofunctor_left_unitality
  Scheme.Modules.pseudofunctor_right_unitality
  CategoryTheory.Bicategory.toNatTrans_conjugateEquiv
  CategoryTheory.unit_conjugateEquiv
  Scheme.Modules.conjugateEquiv_pullbackId_hom
  CategoryTheory.Bicategory.Adjunction.ofCat_comp
  Scheme.Modules.conjugateEquiv_pullbackComp_inv

/-- The canonical morphism `Ω_{Y/S} ⟶ g_* Ω_{X/S}` adjoint to the canonical morphism on
relative differentials of a morphism `g` of schemes over `S`. -/
noncomputable def differentialsSectionMorphism {S : Scheme.{u}} {X Y : Over S} (g : X ⟶ Y) :
    Scheme.Hom.relativeDifferentials Y.hom ⟶
      (Scheme.Modules.pushforward g.left).obj (Scheme.Hom.relativeDifferentials X.hom) :=
  (Scheme.Modules.pullbackPushforwardAdjunction g.left).unit.app
      (Scheme.Hom.relativeDifferentials Y.hom) ≫
    (Scheme.Modules.pushforward g.left).map
      (Scheme.Hom.relativeDifferentialsMap g.left Y.hom X.hom (𝟙 S) (by simp [Over.w g]))

/-- The canonical morphism on relative differentials of the square with both edges the identity
is the pullback unitor. -/
lemma relativeDifferentialsMap_id_overBase {S : Scheme.{u}} (T : Over S) :
    Scheme.Hom.relativeDifferentialsMap (𝟙 T.left) T.hom T.hom (𝟙 S) (by simp) =
      (Scheme.Modules.pullbackId T.left).hom.app
        (Scheme.Hom.relativeDifferentials T.hom) := by
  let M := Scheme.Hom.relativeDifferentials T.hom
  have hdiff : Scheme.Hom.IsRelativeDifferentialsMap (𝟙 T.left) T.hom T.hom
      ((Scheme.Modules.pullbackId T.left).hom.app M) := by
    intro U h
    show (((Scheme.Modules.pullbackPushforwardAdjunction (𝟙 T.left)).homEquiv
        M M ((Scheme.Modules.pullbackId T.left).hom.app M)).val.app (op U)).hom
        ((Scheme.Hom.universalRelativeDerivation T.hom).d h) = _
    rw [Adjunction.homEquiv_unit, pullbackId_unit M]
    show (Scheme.Modules.Hom.app ((Scheme.Modules.pushforwardId T.left).inv.app M) U)
      ((Scheme.Hom.universalRelativeDerivation T.hom).d h) = _
    rw [Scheme.Modules.pushforwardId_inv_app_app]
    rfl
  exact ((Scheme.Hom.isRelativeDifferentialsMap_iff_eq (𝟙 T.left) T.hom T.hom (𝟙 S) (by simp)
    ((Scheme.Modules.pullbackId T.left).hom.app M)).mp hdiff).symm

/-- The canonical morphisms on relative differentials of two composable squares with identity
base edge compose to the canonical morphism of the composite square. -/
lemma relativeDifferentialsMap_comp_overBase {S : Scheme.{u}} {X Y Z : Over S}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (Scheme.Modules.pullbackComp f.left g.left).inv.app _ ≫
      (Scheme.Modules.pullback f.left).map
        (Scheme.Hom.relativeDifferentialsMap g.left Z.hom Y.hom (𝟙 S) (by simp [Over.w g])) ≫
      Scheme.Hom.relativeDifferentialsMap f.left Y.hom X.hom (𝟙 S) (by simp [Over.w f]) =
    Scheme.Hom.relativeDifferentialsMap (f.left ≫ g.left) Z.hom X.hom (𝟙 S)
      (by simp [Category.assoc, Over.w f, Over.w g]) :=
  (Scheme.Hom.IsRelativeDifferentialsMap.comp
    (Scheme.Hom.isRelativeDifferentialsMap_relativeDifferentialsMap g.left Z.hom Y.hom (𝟙 S)
      (by simp [Over.w g]))
    (Scheme.Hom.isRelativeDifferentialsMap_relativeDifferentialsMap f.left Y.hom X.hom (𝟙 S)
      (by simp [Over.w f]))).eq_relativeDifferentialsMap (𝟙 S)
    (by simp [Category.assoc, Over.w f, Over.w g])

/-- The adjoint morphism on relative differentials is compatible with composition. -/
private lemma differentialsSectionMorphism_comp {S : Scheme.{u}} {X Y Z : Over S}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    differentialsSectionMorphism (f ≫ g) =
      differentialsSectionMorphism g ≫
        (Scheme.Modules.pushforward g.left).map (differentialsSectionMorphism f) ≫
        (Scheme.Modules.pushforwardComp f.left g.left).hom.app
          (Scheme.Hom.relativeDifferentials X.hom) := by
  let M := Scheme.Hom.relativeDifferentials Z.hom
  let c_g := Scheme.Hom.relativeDifferentialsMap g.left Z.hom Y.hom (𝟙 S) (by simp [Over.w g])
  let c_f := Scheme.Hom.relativeDifferentialsMap f.left Y.hom X.hom (𝟙 S) (by simp [Over.w f])
  unfold differentialsSectionMorphism
  simp only [Over.comp_left]
  rw [← relativeDifferentialsMap_comp_overBase f g, Functor.map_comp]
  have hunit := congrArg
    (fun k : M ⟶ (Scheme.Modules.pushforward (f.left ≫ g.left)).obj
        ((Scheme.Modules.pullback f.left).obj ((Scheme.Modules.pullback g.left).obj M)) =>
      k ≫ (Scheme.Modules.pushforward (f.left ≫ g.left)).map
        ((Scheme.Modules.pullback f.left).map c_g ≫ c_f))
    (pullbackComp_unit f.left g.left M)
  calc
    _ = ((Scheme.Modules.pullbackPushforwardAdjunction (f.left ≫ g.left)).unit.app M ≫
          (Scheme.Modules.pushforward (f.left ≫ g.left)).map
            ((Scheme.Modules.pullbackComp f.left g.left).inv.app M)) ≫
        (Scheme.Modules.pushforward (f.left ≫ g.left)).map
          ((Scheme.Modules.pullback f.left).map c_g ≫ c_f) := by
      cat_disch
    _ = _ := hunit
    _ = _ := by
      simp only [Category.assoc]
      have hn := (Scheme.Modules.pushforwardComp f.left g.left).hom.naturality
        ((Scheme.Modules.pullback f.left).map c_g ≫ c_f)
      simp only [Functor.comp_map] at hn
      rw [← hn]
      have hf := (Scheme.Modules.pullbackPushforwardAdjunction f.left).unit.naturality c_g
      simp only [Functor.comp_map, Functor.id_map] at hf
      simp only [Functor.map_comp, Category.assoc]
      simp only [← Category.assoc, ← Functor.map_comp]
      rw [Functor.map_comp (Scheme.Modules.pushforward f.left)
        ((Scheme.Modules.pullback f.left).map c_g) c_f]
      simp only [← Category.assoc]
      rw [← hf]

/-- The canonical pullback map on the global sections of the sheaves of relative differentials
induced by a morphism of schemes over `S`. -/
noncomputable def differentialSectionsMap {S : Scheme.{u}} {X Y : Over S} (g : X ⟶ Y) :
    Γ(Scheme.Hom.relativeDifferentials Y.hom, ⊤) ⟶
      Γ(Scheme.Hom.relativeDifferentials X.hom, ⊤) :=
  (differentialsSectionMorphism g).app ⊤ ≫
    (Scheme.Hom.relativeDifferentials X.hom).presheaf.map (eqToHom (by simp)).op

/-- The map on global sections of relative differentials induced by an identity is the
identity. -/
lemma differentialSectionsMap_id {S : Scheme.{u}} (T : Over S) :
    differentialSectionsMap (𝟙 T) = 𝟙 _ := by
  have hsm : differentialsSectionMorphism (𝟙 T) =
      (Scheme.Modules.pushforwardId T.left).inv.app
        (Scheme.Hom.relativeDifferentials T.hom) := by
    unfold differentialsSectionMorphism
    simp only [Over.id_left]
    rw [relativeDifferentialsMap_id_overBase]
    exact pullbackId_unit _
  unfold differentialSectionsMap
  rw [hsm]
  simp only [Scheme.Modules.pushforwardId_inv_app_app, TopologicalSpace.Opens.map_top,
    Functor.id_obj, Functor.op_obj]
  convert (Scheme.Hom.relativeDifferentials T.hom).presheaf.map_id
    (op (⊤ : T.left.Opens)) using 1

/-- The map on global sections of relative differentials induced by a composite is the
composite of the induced maps. -/
lemma differentialSectionsMap_comp {S : Scheme.{u}} {X Y Z : Over S}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    differentialSectionsMap (f ≫ g) =
      differentialSectionsMap g ≫ differentialSectionsMap f := by
  unfold differentialSectionsMap
  rw [differentialsSectionMorphism_comp f g]
  exact topMap_comp f.left g.left
    (Scheme.Hom.relativeDifferentials Z.hom)
    (Scheme.Hom.relativeDifferentials Y.hom)
    (Scheme.Hom.relativeDifferentials X.hom)
    (differentialsSectionMorphism g) (differentialsSectionMorphism f)

/-- An abelian presheaf on schemes over `S` whose value at `T ⟶ S` is the group of global
sections of the sheaf of relative differentials of `T` over `S`, with restriction maps the
canonical ones. -/
structure RelativeDifferentialsPresheaf (S : Scheme.{u}) where
  /-- The abelian-group-valued functor. -/
  functor : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{u}
  /-- Its value at `T` is `Γ(T, Ω_{T/S})`. -/
  objIso (T : (Over S)ᵒᵖ) :
    functor.obj T ≅ Γ(Scheme.Hom.relativeDifferentials T.unop.hom, ⊤)
  /-- Restriction is the canonical pullback map on relative differentials. -/
  map_objIso {T U : (Over S)ᵒᵖ} (g : T ⟶ U) :
    (objIso T).inv ≫ functor.map g ≫ (objIso U).hom = differentialSectionsMap g.unop

/-- The presheaf `T ↦ Γ(T, Ω_{T/S})` on schemes over `S`. -/
@[implicit_reducible]
noncomputable def relativeDifferentialsPresheaf (S : Scheme.{u}) :
    RelativeDifferentialsPresheaf S where
  functor :=
    { obj := fun T => AddCommGrpCat.of Γ(Scheme.Hom.relativeDifferentials T.unop.hom, ⊤)
      map := fun {_ _} g => differentialSectionsMap g.unop
      map_id := fun T => differentialSectionsMap_id T.unop
      map_comp := fun f g => differentialSectionsMap_comp g.unop f.unop }
  objIso _ := Iso.refl _
  map_objIso _ := by simp

end AlgebraicGeometry

end
