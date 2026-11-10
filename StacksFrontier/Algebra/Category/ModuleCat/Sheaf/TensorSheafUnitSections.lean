module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationStalk
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorUnitSections

/-!
# The unitors of the tensor product sheaf, computed on sections

The tensor product `F ⊗_{𝒪_X} G` of two sheaves of `𝒪_X`-modules on a ringed space is the
sheafification of `U ↦ F(U) ⊗_{𝒪_X(U)} G(U)` (Tag 01CA). Its right unitor, built as the
sheafification of the presheaf-level unitor followed by the counit of the sheafification
adjunction, sends the local section `s ⊗ r` of `F ⊗_{𝒪_X} 𝒪_X` to `r • s`.

## Main results

* `Stacks.SheafOfModules.TensorUnit.tensorSheafUnitRightIso_hom_toTensorSheafSection`: the right
  unitor on sections, `s ⊗ r ↦ r • s`.
* `Stacks.SheafOfModules.TensorUnit.presheaf_leftUnitor_app` and
  `Stacks.SheafOfModules.TensorUnit.presheaf_rightUnitor_app`: the presheaf-level unitors on
  pure tensors.
* `Stacks.SheafOfModules.TensorUnit.sheafifyMap_sheafifyValIso_sheafifyUnit`: the sheafification
  of a morphism `f : P ⟶ F.val` into a sheaf, composed with the counit, agrees with `f` on the
  image of the sheafification unit.
* `Stacks.SheafOfModules.TensorUnit.isLocallySurjective_sheafifyUnit` and
  `Stacks.SheafOfModules.TensorUnit.exists_sieve_sum_toTensorSheafSection`: a section of
  `F ⊗_{𝒪_X} G` is, on a covering sieve, a finite sum of pure tensors.

## Implementation notes

`tensorSheafUnitRightIso_hom_toTensorSheafSection` is stated at the explicit composite
`(sheafifyFunctor X).mapIso (ρ_ F.val) ≪≫ sheafifyValIso …`, which is the definition of
`AlgebraicGeometry.SheafOfModules.tensorSheafUnitRightIso`, so it applies to that isomorphism
without importing it.

`AlgebraicGeometry.tensorSheafUnitLeft`, the left unitor obtained from the monoidal structure
localized along sheafification, is a different morphism `𝒪_X ⊗ F ⟶ F` and is not compared with
`AlgebraicGeometry.SheafOfModules.tensorSheafUnitLeftIso` here.

`SheafOfModules.unit` is not syntactically the monoidal unit on presheaves of modules but
coincides with it definitionally, so `λ_ F.val` and `ρ_ F.val` typecheck at the Tag 01CB types
with no transport.

For `Y : AlgebraicGeometry.Scheme` and `M : Y.Modules` the statements apply at
`Y.toRingedSpace`, but the scalar must be spelled `r : Y.ringCatSheaf.obj.obj U`: instance search
does not unfold `Scheme.ringCatSheaf` and so does not find the action on `M.val.obj U` of a scalar
of `(Stacks.SheafOfModules.TensorStalkRingedSpace.O Y.toRingedSpace).obj U`.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
-/

@[expose] public section

open CategoryTheory MonoidalCategory TensorProduct

universe u

noncomputable section

namespace Stacks.SheafOfModules.TensorUnit

variable (X : AlgebraicGeometry.RingedSpace.{u, u})
  (F : SheafOfModules.{u} (structureSheafRing X))

/-- Sheafification is natural in the sheafification unit: the sheafification of a morphism of
presheaves of modules, read on the image of a local section under the unit, is the unit of the
image of that section. -/
public theorem sheafifyFunctor_map_sheafifyUnit
    {P Q : PresheafOfModules.{u} (Stacks.SheafOfModules.TensorStalkRingedSpace.O X)} (f : P ⟶ Q)
    (U : (TopologicalSpace.Opens X.carrier)ᵒᵖ) (x : P.obj U) :
    ((Stacks.SheafOfModules.TensorStalkRingedSpace.sheafifyFunctor X).map f).val.app U
        ((Stacks.SheafOfModules.TensorStalkRingedSpace.sheafifyUnit X P).app U x) =
      (Stacks.SheafOfModules.TensorStalkRingedSpace.sheafifyUnit X Q).app U (f.app U x) :=
  (congrArg (fun k ↦ k.app U x)
    ((Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction X.presheaf
      (structureSheafRing X).property).unit.naturality
      f)).symm

/-- The counit of the sheafification adjunction undoes the sheafification unit on sections of a
sheaf. -/
public theorem sheafifyValIso_hom_sheafifyUnit
    (U : (TopologicalSpace.Opens X.carrier)ᵒᵖ) (s : F.val.obj U) :
    (Stacks.SheafOfModules.sheafifyValIso X.presheaf
          (structureSheafRing X).property
          F).hom.val.app U
        ((Stacks.SheafOfModules.TensorStalkRingedSpace.sheafifyUnit X F.val).app U s) = s :=
  congrArg (fun k ↦ k.app U s)
    ((Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction X.presheaf
      (structureSheafRing
      X).property).right_triangle_components F)

/-- For a morphism `f : P ⟶ F.val` of presheaves of modules into the underlying presheaf of a
sheaf, the induced morphism `P^# ⟶ F` agrees with `f` on the image of the sheafification
unit. -/
public theorem sheafifyMap_sheafifyValIso_sheafifyUnit
    {P : PresheafOfModules.{u} (Stacks.SheafOfModules.TensorStalkRingedSpace.O X)} (f : P ⟶ F.val)
    (U : (TopologicalSpace.Opens X.carrier)ᵒᵖ) (x : P.obj U) :
    ((Stacks.SheafOfModules.TensorStalkRingedSpace.sheafifyFunctor X).map f ≫
          (Stacks.SheafOfModules.sheafifyValIso X.presheaf
            (structureSheafRing X).property
            F).hom).val.app U
        ((Stacks.SheafOfModules.TensorStalkRingedSpace.sheafifyUnit X P).app U x) = f.app U x :=
  (congrArg ((Stacks.SheafOfModules.sheafifyValIso X.presheaf
        (structureSheafRing X).property F).hom.val.app
        U)
      (sheafifyFunctor_map_sheafifyUnit X f U x)).trans
    (sheafifyValIso_hom_sheafifyUnit X F U (f.app U x))

/-- The left unitor of the presheaf tensor product on sections: `r ⊗ s ↦ r • s`. -/
public theorem presheaf_leftUnitor_app
    (U : (TopologicalSpace.Opens X.carrier)ᵒᵖ)
    (r : (Stacks.SheafOfModules.TensorStalkRingedSpace.O X).obj U) (s : F.val.obj U) :
    (MonoidalCategoryStruct.leftUnitor
        (self := (Stacks.SheafOfModules.Tensor.ringSheafPresheafMonoidalCategory
          ⟨X.presheaf, X.IsSheaf⟩).toMonoidalCategoryStruct) F.val).hom.app U
      (r ⊗ₜ[(Stacks.SheafOfModules.TensorStalkRingedSpace.O X).obj U] s) = r • s :=
  TensorProduct.lid_tmul s r

/-- The right unitor of the presheaf tensor product on sections: `s ⊗ r ↦ r • s`. -/
public theorem presheaf_rightUnitor_app
    (U : (TopologicalSpace.Opens X.carrier)ᵒᵖ)
    (s : F.val.obj U) (r : (Stacks.SheafOfModules.TensorStalkRingedSpace.O X).obj U) :
    (MonoidalCategoryStruct.rightUnitor
        (self := (Stacks.SheafOfModules.Tensor.ringSheafPresheafMonoidalCategory
          ⟨X.presheaf, X.IsSheaf⟩).toMonoidalCategoryStruct) F.val).hom.app U
      (s ⊗ₜ[(Stacks.SheafOfModules.TensorStalkRingedSpace.O X).obj U] r) = r • s :=
  TensorProduct.rid_tmul s r

/-- The right unitor of the tensor product sheaf on sections: the canonical map
`F ⊗_{𝒪_X} 𝒪_X ⟶ F` sends the image of the local pure tensor `s ⊗ r` to `r • s`. -/
public theorem tensorSheafUnitRightIso_hom_toTensorSheafSection
    (U : (TopologicalSpace.Opens X.carrier)ᵒᵖ)
    (s : F.val.obj U) (r : (Stacks.SheafOfModules.TensorStalkRingedSpace.O X).obj U) :
    ((Stacks.SheafOfModules.TensorStalkRingedSpace.sheafifyFunctor X).mapIso
        (MonoidalCategoryStruct.rightUnitor
        (self := (Stacks.SheafOfModules.Tensor.ringSheafPresheafMonoidalCategory
          ⟨X.presheaf, X.IsSheaf⟩).toMonoidalCategoryStruct) F.val) ≪≫
          Stacks.SheafOfModules.sheafifyValIso X.presheaf
            (structureSheafRing X).property
            F).hom.val.app U
        (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection X F
          (_root_.SheafOfModules.unit
          (structureSheafRing X)) U
          (s ⊗ₜ[X.presheaf.obj U] r)) = r • s :=
  (sheafifyMap_sheafifyValIso_sheafifyUnit X F
      (MonoidalCategoryStruct.rightUnitor
        (self := (Stacks.SheafOfModules.Tensor.ringSheafPresheafMonoidalCategory
          ⟨X.presheaf, X.IsSheaf⟩).toMonoidalCategoryStruct) F.val).hom U
      (s ⊗ₜ[(Stacks.SheafOfModules.TensorStalkRingedSpace.O X).obj U] r)).trans
    (presheaf_rightUnitor_app X F U s r)

/-- The sheafification unit of a presheaf of modules is locally surjective: every local section
of the sheafification is, on a covering sieve, the image of a section of the presheaf. -/
public theorem isLocallySurjective_sheafifyUnit
    (P : PresheafOfModules.{u} (Stacks.SheafOfModules.TensorStalkRingedSpace.O X)) :
    Presheaf.IsLocallySurjective (Stacks.SheafOfModules.TensorStalkRingedSpace.JX X)
      ((PresheafOfModules.toPresheaf (Stacks.SheafOfModules.TensorStalkRingedSpace.O X)).map
        (Stacks.SheafOfModules.TensorStalkRingedSpace.sheafifyUnit X P)) := by
  change Presheaf.IsLocallySurjective (Stacks.SheafOfModules.TensorStalkRingedSpace.JX X)
    (CategoryTheory.toSheafify (Stacks.SheafOfModules.TensorStalkRingedSpace.JX X)
      ((PresheafOfModules.toPresheaf (Stacks.SheafOfModules.TensorStalkRingedSpace.O X)).obj P))
  infer_instance

/-- A section of the tensor product sheaf is locally a finite sum of pure tensors: for every
section `t` of `F ⊗_{𝒪_X} G` over `U` there is a covering sieve of `U` on each of whose members
`t` restricts to `∑ j, a j ⊗ b j` for finitely many local sections `a j` of `F` and `b j` of
`G`. -/
public theorem exists_sieve_sum_toTensorSheafSection
    (G : SheafOfModules.{u} (structureSheafRing X))
    (U : TopologicalSpace.Opens X.carrier)
    (t : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj
      (F)).obj (G))).val.obj (Opposite.op U)) :
    ∃ S : Sieve U, S ∈ Stacks.SheafOfModules.TensorStalkRingedSpace.JX X U ∧
      ∀ ⦃V : TopologicalSpace.Opens X.carrier⦄ (k : V ⟶ U), S.arrows k →
        ∃ (n : ℕ) (a : Fin n → F.val.obj (Opposite.op V))
          (b : Fin n → G.val.obj (Opposite.op V)),
          ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj
            (F)).obj (G))).val.map k.op t =
            ∑ j, Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection X F G
            (Opposite.op V)
              (a j ⊗ₜ[X.presheaf.obj (Opposite.op V)] b j) := by
  refine ⟨_, (isLocallySurjective_sheafifyUnit X
    ((PresheafOfModules.tensorObj (O := (X).presheaf) (F.val) (G.val)))).imageSieve_mem t,
    fun V k ⟨z, hz⟩ => ?_⟩
  obtain ⟨n, a, b, hab⟩ := TensorProduct.exists_sum_tmul_eq z
  refine ⟨n, a, b, hz.symm.trans ?_⟩
  rw [hab]
  exact map_sum ((Stacks.SheafOfModules.TensorStalkRingedSpace.sheafifyUnit X
    ((PresheafOfModules.tensorObj (O := (X).presheaf) (F.val) (G.val)))).app (Opposite.op
    V)).hom _ Finset.univ

end Stacks.SheafOfModules.TensorUnit

end

end
