module

public import StacksFrontier.Cotangent.SchemeOverRing
public import StacksFrontier.Cotangent.SheavesOfRings.SectionwiseSheafificationPresheafBase

/-!
# The cotangent complex of a scheme over a ring as a sheafification

Let `Λ` be a ring and let `X` be a scheme over `Λ`. On the small Zariski site of `X` the
cotangent complex `L_{𝒪_X/Λ̲}` of the `Λ`-algebra structure `Λ̲ ⟶ 𝒪_X` over the constant sheaf
is the sheafification of the rule `U ↦ L_{𝒪_X(U)/Λ}`, the cotangent complexes of the ring maps
`Λ → 𝒪_X(U)`. This is Remark 08SX over the constant presheaf `U ↦ Λ`, which maps to `Λ̲` by the
unit of sheafification, and it is the form in which the proof of Tag 08T9 uses Remark 08SX. It is
not the sheafification of `U ↦ L_{𝒪_X(U)/Λ̲(U)}` of Remark 08SX itself: the ring `Λ̲(U)` of
locally constant functions on `U` differs from `Λ` when `U` is disconnected.

## Main definitions

* `AlgebraicGeometry.SchemeOverRing.constantBasePresheaf` is the constant presheaf `U ↦ Λ` of
  rings on `X`, and `AlgebraicGeometry.SchemeOverRing.constantBasePresheafToSheaf` its map to the
  constant sheaf `Λ̲`, the unit of sheafification.
* `AlgebraicGeometry.SchemeOverRing.sectionwiseCotangentComplexConstant` is the complex of
  presheaves of `𝒪_X`-modules `U ↦ L_{𝒪_X(U)/Λ}`.

## Main results

* `AlgebraicGeometry.SchemeOverRing.sectionwiseCotangentComplexConstant_X_obj`: its term in
  degree `j` over `U` is the degree-`j` term of the cotangent complex of the ring map
  `Λ → 𝒪_X(U)`.
* `AlgebraicGeometry.SchemeOverRing.sheafifiedSectionwiseCotangentComplexConstantIso`: the
  degreewise sheafification of `U ↦ L_{𝒪_X(U)/Λ}` is `L_{𝒪_X/Λ̲}`, as complexes of sheaves of
  `𝒪_X`-modules, and `sheafifiedSectionwiseCotangentComplexConstantAbIso` the same statement on
  abelian groups.

## References

* [Stacks Project, Tag 08SX](https://stacks.math.columbia.edu/tag/08SX)
* [Stacks Project, Tag 08T9](https://stacks.math.columbia.edu/tag/08T9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.SchemeOverRing

variable (Λ : Type u) [CommRing Λ] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of Λ))

/-- The constant presheaf `U ↦ Λ` of commutative rings on the small Zariski site of `X`. -/
abbrev constantBasePresheaf (X : Scheme.{u}) : (Opens ↥X)ᵒᵖ ⥤ CommRingCat.{u} :=
  (Functor.const _).obj (CommRingCat.of Λ)

/-- The map from the constant presheaf `U ↦ Λ` to the constant sheaf `Λ̲`, its sheafification:
the unit of sheafification. -/
def constantBasePresheafToSheaf (X : Scheme.{u}) :
    constantBasePresheaf Λ X ⟶ (constantBaseSheaf Λ X).obj :=
  toSheafify (Opens.grothendieckTopology ↥X) (constantBasePresheaf Λ X)

/-- The map from the constant presheaf `U ↦ Λ` to the constant sheaf `Λ̲` is inverted by
sheafification. -/
theorem W_constantBasePresheafToSheaf (X : Scheme.{u}) :
    (Opens.grothendieckTopology ↥X).W (constantBasePresheafToSheaf Λ X) :=
  (Opens.grothendieckTopology ↥X).W_toSheafify _

/-- The complex of presheaves of `𝒪_X`-modules `U ↦ L_{𝒪_X(U)/Λ}`: over `U` it is the cotangent
complex of the ring map `Λ → Λ̲(U) → 𝒪_X(U)`, with the maps induced by the restriction maps of
`𝒪_X` as restriction maps. -/
abbrev sectionwiseCotangentComplexConstant :
    CochainComplex (PresheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (structureSheafOfSite X)).obj) ℤ :=
  CategoryTheory.Sheaf.presheafBaseCotangentModuleComplex.{u, u, u}
    (Opens.grothendieckTopology ↥X) (constantStructureMap Λ p) (constantBasePresheafToSheaf Λ X)

/-- Over `U`, the degree-`j` term of `U ↦ L_{𝒪_X(U)/Λ}` is the degree-`j` term of the cotangent
complex `L_{𝒪_X(U)/Λ}` of the `Λ`-algebra `𝒪_X(U)`, with the structure map
`Λ → Λ̲(U) → 𝒪_X(U)`. -/
theorem sectionwiseCotangentComplexConstant_X_obj (j : ℤ) (U : (Opens ↥X)ᵒᵖ) :
    ((sectionwiseCotangentComplexConstant Λ p).X j).obj U =
      letI : Algebra Λ ((structureSheafOfSite X).obj.obj U) :=
        ((constantBasePresheafToSheaf Λ X).app U ≫
          (constantStructureMap Λ p).hom.app U).hom.toAlgebra
      (CommAlgCat.cotangentComplex.{u, u} Λ
        (CommAlgCat.of Λ ((structureSheafOfSite X).obj.obj U))).X j :=
  rfl

/-- **Tag 08SX over the base `U ↦ Λ`, the form used in Tag 08T9.** On the small Zariski site of a
scheme `X` over `Λ`, the cotangent complex `L_{𝒪_X/Λ̲}` of the `Λ`-algebra structure of `𝒪_X`
over the constant sheaf is the sheafification of `U ↦ L_{𝒪_X(U)/Λ}`: the degreewise
sheafification of the complex of presheaves of `𝒪_X`-modules `U ↦ L_{𝒪_X(U)/Λ}` is isomorphic
to `L_{𝒪_X/Λ̲}` as a complex of sheaves of `𝒪_X`-modules, in each degree by the adjunct of the
canonical map `L_{𝒪_X(U)/Λ} ⟶ L_{𝒪_X(U)/Λ̲(U)} ⟶ L_{𝒪_X/Λ̲}(U)`. -/
def sheafifiedSectionwiseCotangentComplexConstantIso :
    ((PresheafOfModules.sheafification.{u}
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u}
          (structureSheafOfSite X)).obj)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (sectionwiseCotangentComplexConstant Λ p) ≅
      cotangentComplexConstant Λ p :=
  CategoryTheory.Sheaf.sheafifiedPresheafBaseCotangentComplexIso.{u, u, u} _ _ _
    (W_constantBasePresheafToSheaf Λ X)

/-- **Tag 08SX over the base `U ↦ Λ`, on abelian groups.** The sheafification of the presheaf of
complexes of abelian groups `U ↦ L_{𝒪_X(U)/Λ}` is isomorphic to `L_{𝒪_X/Λ̲}`, by the canonical
maps followed by the counit of sheafification. -/
def sheafifiedSectionwiseCotangentComplexConstantAbIso :
    ((presheafToSheaf (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u}).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
      (CategoryTheory.Sheaf.sectionwiseCotangentPresheafComplex.{u, u, u} ⊥
        (CategoryTheory.Sheaf.presheafBaseHom.{u, u, u} (Opens.grothendieckTopology ↥X)
          (constantStructureMap Λ p) (constantBasePresheafToSheaf Λ X))) ≅
      CategoryTheory.Sheaf.cotangentComplexAb.{u, u, u} (Opens.grothendieckTopology ↥X)
        (constantStructureMap Λ p) :=
  CategoryTheory.Sheaf.sheafifiedPresheafBaseCotangentPresheafComplexIso.{u, u, u} _ _ _
    (W_constantBasePresheafToSheaf Λ X)

end AlgebraicGeometry.SchemeOverRing

end
