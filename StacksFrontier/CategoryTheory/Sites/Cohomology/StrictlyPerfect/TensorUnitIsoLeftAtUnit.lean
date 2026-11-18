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

/-- The naturality square of the left unit constraint, with both constraints unfolded: it
combines the naturality of the presheaf left unitor with that of the counit of
`sheafificationForgetAdjunction`. -/
lemma sheafification_map_leftUnitor_counit_naturality
    {M M' : SheafOfModules.{w} (ringSheaf R)} (f : M ⟶ M') :
    (sheafification R).map (𝟙_ (PresheafOfModules (ringSheaf R).obj) ◁ f.val) ≫
        (sheafification R).map (λ_ M'.val).hom ≫ (sheafificationForgetAdjunction R).counit.app M' =
      ((sheafification R).map (λ_ M.val).hom ≫ (sheafificationForgetAdjunction R).counit.app M) ≫
        f :=
  calc _ = (sheafification R).map ((λ_ M.val).hom ≫ f.val) ≫
        (sheafificationForgetAdjunction R).counit.app M' := by
          rw [← MonoidalCategory.leftUnitor_naturality]; exact (Functor.map_comp_assoc _ _ _ _).symm
    _ = (sheafification R).map (λ_ M.val).hom ≫ (sheafification R).map f.val ≫
        (sheafificationForgetAdjunction R).counit.app M' := Functor.map_comp_assoc _ _ _ _
    _ = _ := (congrArg _ ((sheafificationForgetAdjunction R).counit.naturality f)).trans
        (Category.assoc _ _ _).symm

/-- **The left unit constraint as a natural isomorphism** `O ⊗ - ≅ 𝟭`: its naturality is that of
the presheaf left unitor and of the counit of `sheafificationForgetAdjunction`. -/
def sheafTensorUnitNatIsoLeft :
    (sheafTensor R).obj (SheafOfModules.unit (ringSheaf R)) ≅
      𝟭 (SheafOfModules.{w} (ringSheaf R)) :=
  NatIso.ofComponents (sheafTensorUnitIsoLeft R)
    fun f => sheafification_map_leftUnitor_counit_naturality R f

end Stacks.SheafOfModules.Tensor

end
