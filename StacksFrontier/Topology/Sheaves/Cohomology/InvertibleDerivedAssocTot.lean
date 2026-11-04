module

public import StacksFrontier.Topology.Sheaves.Modules.AssociatedSheaf.TensorNaturality
public import StacksFrontier.Topology.Sheaves.Cohomology.InvertibleDerivedAssociated
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalSheafTensor
public import StacksFrontier.Homology.TotalComplexTransport

/-!
# Construction (3) of Stacks 01BH and the total tensor complex

For bounded complexes `P`, `P'` of modules over `R = Γ(Y, 𝒪_Y)`, the associated complexes of
sheaves satisfy `ℱ(Tot(P ⊗_R P')) ≅ Tot(ℱP ⊗_{𝒪_Y} ℱP')`.

## References

* [Stacks Project, Tag 01BH](https://stacks.math.columbia.edu/tag/01BH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open Opposite TopologicalSpace Stacks.SheafOfModules.DerivedMonoidal Stacks.AssociatedSheaf

universe u

namespace Stacks.Cohomology.InvertibleDerived

variable (Y : RingedSpace.{u, u})

/-- **Construction (3) carries the tensor product to the sheaf tensor bifunctor.**

This is `Stacks.AssociatedSheaf.associatedSheafTensorIso` over the global sections of `𝒪_Y`,
seated at the sheaf tensor bifunctor of `Y.sheaf`. -/
public def assocTensorSheafTensorIso (M N : ModuleCat.{u} (GlobalRing Y)) :
    (assocF Y).obj (M ⊗ N) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨(Y).presheaf, (Y).IsSheaf⟩).obj ((assocF Y).obj M)).obj
        ((assocF Y).obj N) :=
  associatedSheafTensorIso Y (RingHom.id (GlobalRing Y)) M N

/-- Naturality of `Stacks.AssociatedSheaf.associatedSheafTensorIso` in its first variable, over
the global sections of `𝒪_Y`, with the sheaf tensor bifunctor on the right. This is the
square `Functor.mapBifunctorTotalIso` asks for. -/
public theorem associatedSheafTensorIso_naturality_left {M M' : ModuleCat.{u} (GlobalRing Y)}
    (f : M ⟶ M') (N : ModuleCat.{u} (GlobalRing Y)) :
    (associatedSheafFunctor.{u, u} Y (RingHom.id (GlobalRing Y))).map (f ▷ N) ≫
        (associatedSheafTensorIso Y (RingHom.id (GlobalRing Y)) M' N).hom =
      (associatedSheafTensorIso Y (RingHom.id (GlobalRing Y)) M N).hom ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨(Y).presheaf, (Y).IsSheaf⟩).map
            ((associatedSheafFunctor.{u, u} Y (RingHom.id (GlobalRing Y))).map f)).app
          ((associatedSheafFunctor.{u, u} Y (RingHom.id (GlobalRing Y))).obj N) :=
  assocTensorIso_naturality_left Y (RingHom.id (GlobalRing Y)) f N

/-- Naturality of `Stacks.AssociatedSheaf.associatedSheafTensorIso` in its second variable, over
the global sections of `𝒪_Y`, with the sheaf tensor bifunctor on the right. -/
public theorem associatedSheafTensorIso_naturality_right (M : ModuleCat.{u} (GlobalRing Y))
    {N N' : ModuleCat.{u} (GlobalRing Y)} (g : N ⟶ N') :
    (associatedSheafFunctor.{u, u} Y (RingHom.id (GlobalRing Y))).map (M ◁ g) ≫
        (associatedSheafTensorIso Y (RingHom.id (GlobalRing Y)) M N').hom =
      (associatedSheafTensorIso Y (RingHom.id (GlobalRing Y)) M N).hom ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨(Y).presheaf, (Y).IsSheaf⟩).obj
            ((associatedSheafFunctor.{u, u} Y (RingHom.id (GlobalRing Y))).obj M)).map
          ((associatedSheafFunctor.{u, u} Y (RingHom.id (GlobalRing Y))).map g) :=
  assocTensorIso_naturality_right Y (RingHom.id (GlobalRing Y)) M g

/-- Construction (3) of Stacks 01BH, with values in sheaves of modules over the ring sheaf. -/
public def assocR : ModuleCat.{u} (GlobalRing Y) ⥤
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf) :=
  assocF Y

/-- Construction (3) is an additive functor. -/
public instance assocR_additive : (assocR Y).Additive :=
  ⟨fun {_ _ f g} => (assocF Y).map_add (f := f) (g := g)⟩

/-- Construction (3) preserves colimits, being a left adjoint. -/
public instance assocR_preservesColimits : PreservesColimitsOfSize.{0, 0} (assocR Y) :=
  (assocAdj Y).leftAdjoint_preservesColimits

/-- The sheaf tensor bifunctor preserves zero morphisms, being additive. -/
public instance sheafTensor_preservesZeroMorphisms :
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨(Y).presheaf, (Y).IsSheaf⟩).PreservesZeroMorphisms :=
  @Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
    (Stacks.SheafOfModules.Tensor.sheafTensor_additive
      (J := Opens.grothendieckTopology Y.carrier) Y.sheaf)

/-- Tensoring with a fixed sheaf of modules preserves zero morphisms, being additive. -/
public instance sheafTensor_obj_preservesZeroMorphisms
    (A : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨(Y).presheaf, (Y).IsSheaf⟩).obj A).PreservesZeroMorphisms :=
  @Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf).obj A)
    (Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive
      (J := Opens.grothendieckTopology Y.carrier) Y.sheaf A)

/-- **Construction (3) carries the total tensor complex to the total tensor complex.** -/
public def assocTotIso (P P' : CochainComplex (ModuleCat.{u} (GlobalRing Y)) ℤ) :
    letI : (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        Y.sheaf).PreservesZeroMorphisms :=
      sheafTensor_preservesZeroMorphisms Y
    letI : ∀ A : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf),
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf).obj
          A).PreservesZeroMorphisms :=
      fun A => sheafTensor_obj_preservesZeroMorphisms Y A
    ((assocR Y).mapHomologicalComplex (ComplexShape.up ℤ)).obj (P ⊗ P') ≅
      HomologicalComplex.mapBifunctor
        (((assocR Y).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
        (((assocR Y).mapHomologicalComplex (ComplexShape.up ℤ)).obj P')
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf) (ComplexShape.up ℤ) :=
  letI : (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      Y.sheaf).PreservesZeroMorphisms :=
    sheafTensor_preservesZeroMorphisms Y
  letI : ∀ A : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf),
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf).obj
        A).PreservesZeroMorphisms :=
    fun A => sheafTensor_obj_preservesZeroMorphisms Y A
  Functor.mapBifunctorTotalIso (curriedTensor _)
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)
    (assocR Y) (assocR Y) (assocR Y) (associatedSheafTensorIso Y (RingHom.id (GlobalRing Y)))
    (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
    (fun f b => associatedSheafTensorIso_naturality_left Y f b)
    (fun a _ _ g => associatedSheafTensorIso_naturality_right Y a g) P P'

end Stacks.Cohomology.InvertibleDerived

end
