module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.HomologyRestrictionAdjoint
public import StacksFrontier.Cotangent.EtaleSquareCotangentHomology
public import StacksFrontier.Cotangent.SheavesOfRings.SectionwiseCotangentComplexIso
public import StacksFrontier.Cotangent.SheavesOfRings.SectionwiseSheafificationPresheafBase

/-!
# The cohomology sheaves of the cotangent complex over a presheaf of base rings

Let `A ⟶ B` be a homomorphism of sheaves of commutative rings on a site and `R ⟶ A` a map from a
presheaf of commutative rings which is inverted by sheafification. Remark 08SX over the base `R`
(`CategoryTheory.Sheaf.sheafifiedPresheafBaseCotangentComplexIso`) identifies `L_{B/A}` with the
sheafification of the complex of presheaves of `B`-modules `U ↦ L_{B(U)/R(U)}`. This file reads
that identification on cohomology, and records how the presheaf `U ↦ H^i(L_{B(U)/R(U)})` behaves
along a restriction map which is étale with bijective base:

* the cohomology sheaf `H^i(L_{B/A})` is the sheafification of the presheaf of `B`-modules
  `U ↦ H^i(L_{B(U)/R(U)})` (`CategoryTheory.Sheaf.presheafBaseCohomologySheafIso`), sheafification
  being exact;
* the sections of that presheaf over `U` are `H^i(L_{B(U)/R(U)})`
  (`CategoryTheory.Sheaf.presheafBaseHomologyObjIso`), evaluation being exact;
* along `g : U ⟶ V` with `R(U) → R(V)` bijective and `B(U) → B(V)` étale, the adjoint
  `B(V) ⊗_{B(U)} H^i(L_{B(U)/R(U)}) ⟶ H^i(L_{B(V)/R(V)})` of its restriction map is an isomorphism
  (`CategoryTheory.Sheaf.isIso_presheafBaseHomologyRestrictionAdjoint`).

This is the form of Tag 08SW in which the proof of quasi-coherence of `H^i(L_{X/Λ})` uses it: the
base `R` is the constant presheaf `U ↦ Λ` rather than the sheaf `Λ̲`, whose sections over a
disconnected `U` are larger than `Λ`.

## Main definitions

* `CategoryTheory.Sheaf.presheafBaseCohomologySheafIso`
* `CategoryTheory.Sheaf.presheafBaseHomologyObjIso`

## Main results

* `CategoryTheory.Sheaf.isIso_presheafBaseHomologyRestrictionAdjoint`

## References

* [Stacks Project, Tag 08SW](https://stacks.math.columbia.edu/tag/08SW)
* [Stacks Project, Tag 08SX](https://stacks.math.columbia.edu/tag/08SX)
* [Stacks Project, Tag 08R2](https://stacks.math.columbia.edu/tag/08R2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {A B : Sheaf J CommRingCat.{max u v w}} (f : A ⟶ B)
  {R : Cᵒᵖ ⥤ CommRingCat.{max u v w}} (a : R ⟶ A.obj)

/-- **`H^i(L_{B/A})` is the sheafification of `U ↦ H^i(L_{B(U)/R(U)})`**, for a presheaf of base
rings `R ⟶ A` inverted by sheafification: the sheafification functor of presheaves of modules is
exact, so it commutes with cohomology, and the sheafification of the complex
`U ↦ L_{B(U)/R(U)}` is `L_{B/A}` (Remark 08SX over the base `R`). -/
def presheafBaseCohomologySheafIso (ha : J.W a) (i : ℤ) :
    (moduleSheafification J (B := B)).obj
        ((presheafBaseCotangentModuleComplex.{u, v, w} J f a).homology i) ≅
      (cotangentComplex.{u, v, w} J f).homology i :=
  ((StacksDraft.DerivedCategoryHomology.mapHomologicalComplexHomologyIso
      (moduleSheafification J (B := B)) (ComplexShape.up ℤ) i).app
        (presheafBaseCotangentModuleComplex.{u, v, w} J f a)).symm ≪≫
    (HomologicalComplex.homologyFunctor (targetModules J B) (ComplexShape.up ℤ) i).mapIso
      (sheafifiedPresheafBaseCotangentComplexIso.{u, v, w} J f a ha)

/-- Over an object `U` of the site, the complex `U ↦ L_{B(U)/R(U)}` of presheaves of modules is
the cotangent complex of the ring map `R(U) → B(U)`. -/
theorem evaluation_mapHomologicalComplex_presheafBaseCotangentModuleComplex (U : Cᵒᵖ) :
    ((PresheafOfModules.evaluation
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B).obj U).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (presheafBaseCotangentModuleComplex.{u, v, w} J f a) =
      CommAlgCat.cotangentComplex.{max u v w, max u v w} (R.obj U)
        (sectionsAlgebra ⊥ (presheafBaseHom.{u, v, w} J f a) U) :=
  rfl

/-- **The sections of the presheaf `U ↦ H^i(L_{B(U)/R(U)})` over `U` are `H^i(L_{B(U)/R(U)})`**,
evaluation of presheaves of modules being exact. -/
def presheafBaseHomologyObjIso (i : ℤ) (U : Cᵒᵖ) :
    (CommAlgCat.cotangentComplex.{max u v w, max u v w} (R.obj U)
        (sectionsAlgebra ⊥ (presheafBaseHom.{u, v, w} J f a) U)).homology i ≅
      ((presheafBaseCotangentModuleComplex.{u, v, w} J f a).homology i).obj U :=
  (Stacks.Homology.exactHomologyIso
    (PresheafOfModules.evaluation
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B).obj U) i).app
    (presheafBaseCotangentModuleComplex.{u, v, w} J f a)

/-- **Étale base change of `U ↦ H^i(L_{B(U)/R(U)})` along a restriction map.** If along
`g : U ⟶ V` the base `R(U) → R(V)` is bijective and `B(U) → B(V)` is étale, then
`B(V) ⊗_{B(U)} H^i(L_{B(U)/R(U)}) ⟶ H^i(L_{B(V)/R(V)})`, `b ⊗ m ↦ b · m|_V`, is an isomorphism:
`B(V) ⊗_{B(U)} L_{B(U)/R(U)} ⟶ L_{B(V)/R(V)}` is a quasi-isomorphism by Tag 08R2, item (5), and
the fundamental triangle, and `B(U) → B(V)` is flat. -/
theorem isIso_presheafBaseHomologyRestrictionAdjoint (i : ℤ) {U V : Cᵒᵖ} (g : U ⟶ V)
    (hB : (B.obj.map g).hom.Etale) (hA : Function.Bijective (R.map g).hom) :
    IsIso (PresheafOfModules.homologyRestrictionAdjoint B
      (presheafBaseCotangentModuleComplex.{u, v, w} J f a) i g) := by
  have hq := CommAlgCat.quasiIso_squareCotangentExtendScalarsMap_of_etale
    (sectionsRestrictionSquare ⊥ (presheafBaseHom.{u, v, w} J f a) g) hB hA
  have hflat : (PresheafOfModules.sectionRestrictionHom B g).Flat := by
    let : Algebra (B.obj.obj U) (B.obj.obj V) := (B.obj.map g).hom.toAlgebra
    have : Algebra.Etale (B.obj.obj U) (B.obj.obj V) := hB
    exact (inferInstance : Module.Flat (B.obj.obj U) (B.obj.obj V))
  exact PresheafOfModules.isIso_homologyRestrictionAdjoint B
    (presheafBaseCotangentModuleComplex.{u, v, w} J f a) i g hflat hq

end CategoryTheory.Sheaf

end
