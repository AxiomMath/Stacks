module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.TensorOfStrictlyPerfectComplexes
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SheafTensorUnitIsoLeftMaps

/-!
# The left unit constraint of the sheaf tensor product as a natural isomorphism

The left unit constraints `Stacks.SheafOfModules.Tensor.sheafTensorUnitIsoLeft` `O ⊗ M ≅ M` of
the sheaf tensor product are natural in `M`, and so assemble into a natural isomorphism
`O ⊗ - ≅ 𝟭`.  Their compatibilities with maps tensored in the left factor, among them the
agreement `λ_O = ρ_O` at the structure sheaf, are in
`StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SheafTensorUnitIsoLeftMaps`.

## Main definitions

* `Stacks.SheafOfModules.Tensor.sheafTensorUnitNatIsoLeft`: `O ⊗ - ≅ 𝟭` as a natural isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u v w

namespace Stacks.SheafOfModules.Tensor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{w})
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

attribute [local instance] monoidalPresheavesOfModules

/-- **The left unit constraint as a natural isomorphism** `O ⊗ - ≅ 𝟭`: its naturality is that of
the presheaf left unitor and of the sheafification counit. -/
def sheafTensorUnitNatIsoLeft :
    (sheafTensor R).obj (SheafOfModules.unit (ringSheaf R)) ≅
      𝟭 (SheafOfModules.{w} (ringSheaf R)) :=
  NatIso.ofComponents (sheafTensorUnitIsoLeft R) (fun {M M'} f => by
    have hM : (sheafTensorUnitIsoLeft R M).hom =
        (PresheafOfModules.sheafification (R := ringSheaf R) (𝟙 (ringSheaf R).obj)).map
            (λ_ M.val).hom ≫
          (PresheafOfModules.sheafificationAdjunction (R := ringSheaf R)
            (𝟙 (ringSheaf R).obj)).counit.app M := rfl
    have hM' : (sheafTensorUnitIsoLeft R M').hom =
        (PresheafOfModules.sheafification (R := ringSheaf R) (𝟙 (ringSheaf R).obj)).map
            (λ_ M'.val).hom ≫
          (PresheafOfModules.sheafificationAdjunction (R := ringSheaf R)
            (𝟙 (ringSheaf R).obj)).counit.app M' := rfl
    have hT : ((sheafTensor R).obj (SheafOfModules.unit (ringSheaf R))).map f =
        (PresheafOfModules.sheafification (R := ringSheaf R) (𝟙 (ringSheaf R).obj)).map
          ((SheafOfModules.unit (ringSheaf R)).val ◁ f.val) := rfl
    rw [hM, hM', hT]
    set SH := (PresheafOfModules.sheafification (R := ringSheaf R) (𝟙 (ringSheaf R).obj)) with hSH
    set EP := (PresheafOfModules.sheafificationAdjunction (R := ringSheaf R)
      (𝟙 (ringSheaf R).obj)).counit with hEP
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun z => z ≫ EP.app M')
        ((SH.map_comp _ _).symm.trans
          (congrArg (fun z => SH.map z)
            (MonoidalCategory.leftUnitor_naturality f.val)))).trans
        ((congrArg (fun z => z ≫ EP.app M') (SH.map_comp _ _)).trans
          ((Category.assoc _ _ _).trans
            ((congrArg (fun z => SH.map (λ_ M.val).hom ≫ z) (EP.naturality f)).trans
              (Category.assoc _ _ _).symm)))))




end Stacks.SheafOfModules.Tensor

end
