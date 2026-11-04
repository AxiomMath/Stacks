module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPresentations
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.BoxProductLeftOperator
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.OperatorOrderPullbackOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.OperatorTransportIso

/-!
# The box product of the identity with a differential operator, and of two operators

Let `a : X ⟶ S` and `b : Y ⟶ S` be morphisms of schemes. Interchanging the two factors of the
fibre product identifies `F ⊠ G = pr₁^*F ⊗ pr₂^*G` on `X ×_S Y` with the inverse image of
`G ⊠ F = pr₁^*G ⊗ pr₂^*F` on `Y ×_S X` along the symmetry isomorphism, the braiding of the tensor
product of sheaves of modules supplying the interchange of the two tensor factors. So the box
product `1 ⊠ E` of the identity of a quasi-coherent `𝒪_X`-module `F` with a differential operator
`E : G ⟶ G'` of order at most `l` on `Y/S` is the box product `E ⊠ 1` on `Y ×_S X`, read through
that identification: a differential operator of order at most `l` on `X ×_S Y / S`. Composing it
with `D ⊠ 1` gives the box product `D ⊠ E` of two finite-order differential operators, a morphism
of the category of finite-order differential operators on `X ×_S Y / S`.

## Main definitions

* `AlgebraicGeometry.pullbackSwapMor`: the symmetry `X ×_S Y ⟶ Y ×_S X` of a fibre product,
  written as the morphism induced by the two projections in the other order.
* `AlgebraicGeometry.externalTensorProductSwapIso`: the identification of `F ⊠ G` on `X ×_S Y`
  with the inverse image of `G ⊠ F` along the symmetry.
* `AlgebraicGeometry.boxOpRight`: the operator `1 ⊠ E`, as a global operator on local sections.
* `AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory.boxHomRight`: `1 ⊠ E` as a morphism
  of the category of finite-order differential operators on `X ×_S Y / S`.
* `AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory.boxHom`: the box product `D ⊠ E` of
  two morphisms of the categories of finite-order differential operators on `X/S` and on `Y/S`,
  as the composite `(1 ⊠ E) ∘ (D ⊠ 1)`.

## Main results

* `Stacks.SheafOfModules.TensorPresentations.tensorSheafSwap_app_toTensorSheafSection`: the
  braiding of the tensor product of two sheaves of modules on a ringed space interchanges the two
  factors of a pure tensor.
* `AlgebraicGeometry.isGlobalDiffOpOfOrder_boxOpRight`: `1 ⊠ E` is a differential operator of
  order at most `l` on `X ×_S Y / S`.

## Implementation notes

The symmetry is written as `pullback.lift (pullback.snd a b) (pullback.fst a b)` rather than as
`CategoryTheory.Limits.pullbackSymmetry`, so that
`Stacks.Tag01VSPullbackTensor.pullbackLift_externalTensorProductIso` applies to it without a
rewrite; that it is an isomorphism is read off from `pullbackSymmetry`.

The transport of the operator is three conjugations and nothing else: the differential operators
of order at most `l` on `Y ×_S X / S` are those on `X ×_S Y / S` between the restrictions along
the symmetry (`AlgebraicGeometry.globalDiffOpEquivOfIso`), those are the operators between the
inverse images (`AlgebraicGeometry.globalDiffOpEquivRestrictPullback`), and conjugating by
`externalTensorProductSwapIso` moves them to operators between the box products in the original
order (`AlgebraicGeometry.globalDiffOpEquivGlobalOpCongr`). None of these changes the order, and
the composite `X ×_S Y ⟶ Y ×_S X ⟶ S` of the symmetry with the structure morphism is the
structure morphism of `X ×_S Y`, which is what makes the orders match up.

The order of a morphism of `AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory` is
quantified existentially, so `boxHomRight` names an order bound for its argument.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 0G45](https://stacks.math.columbia.edu/tag/0G45)
* [Stacks Project, Tag 0G46](https://stacks.math.columbia.edu/tag/0G46)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct MonoidalCategory
open Stacks.SheafOfModules.TensorStalkRingedSpace
open Stacks.Tag01VSPullbackTensor

universe u

namespace Stacks.SheafOfModules.TensorPresentations

-- Mathlib's symmetric monoidal structure on presheaves of `𝒪_X`-modules is keyed on
-- `𝒪_X ⋙ forget₂ CommRingCat RingCat`, while `F.val` lives in
-- `PresheafOfModules (structureSheafRing X).obj`; a goal is keyed into the typeclass
-- discrimination tree with only `@[reducible]` definitions unfolded, and `structureSheafRing`
-- is `@[instance_reducible]`, so it is not retrieved at this spelling and the tensor product of
-- the structure that is is not `presheafTensor`.  These two declarations are that same
-- structure at the index `F.val` carries; they are declared, non-instance, next door.

/-- **The braiding of a tensor product of sheaves of modules on a pure tensor.** The isomorphism
`F ⊗ G ≅ G ⊗ F` of [Stacks, Tag 01CA] carries the section coming from `m ⊗ n` to the section
coming from `n ⊗ m`. -/
theorem tensorSheafSwap_app_toTensorSheafSection (X : AlgebraicGeometry.RingedSpace.{u, u})
    (F G : SheafOfModules.{u} (structureSheafRing X))
    (U : TopologicalSpace.Opens X.carrier) (m : F.val.obj (op U)) (n : G.val.obj (op U)) :
    ((tensorSheafSwap X F G).hom.val.app (op U)).hom
        (toTensorSheafSection X F G (op U) (m ⊗ₜ[X.presheaf.obj (op U)] n))
      = toTensorSheafSection X G F (op U) (n ⊗ₜ[X.presheaf.obj (op U)] m) := by
  let : MonoidalCategory (PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat RingCat)) :=
    PresheafOfModules.monoidalCategory (R := X.presheaf)
  let : SymmetricCategory (PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat RingCat)) :=
    PresheafOfModules.symmetricCategory (R := X.presheaf)
  unfold toTensorSheafSection tensorSheafSwap
  have hnat := (PresheafOfModules.sheafificationAdjunction (R := structureSheafRing X)
      (𝟙 (structureSheafRing X).obj)).unit.naturality
    (show (PresheafOfModules.tensorObj (O := (X).presheaf) (F.val) (G.val)) ⟶
        (PresheafOfModules.tensorObj (O := (X).presheaf) (G.val) (F.val)) from
      (β_ F.val G.val).hom)
  exact (congrArg (fun α ↦ (PresheafOfModules.Hom.app α (op U)).hom
    (m ⊗ₜ[X.presheaf.obj (op U)] n)) hnat).symm

end Stacks.SheafOfModules.TensorPresentations

namespace AlgebraicGeometry

section Swap

variable {X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)

/-- **The symmetry of a fibre product.** The morphism `X ×_S Y ⟶ Y ×_S X` induced by the second
and the first projection. -/
abbrev pullbackSwapMor : pullback a b ⟶ pullback b a :=
  pullback.lift (pullback.snd a b) (pullback.fst a b) pullback.condition.symm

/-- The symmetry of a fibre product is the canonical commutativity isomorphism. -/
theorem pullbackSwapMor_eq : pullbackSwapMor a b = (pullbackSymmetry a b).hom := by
  apply pullback.hom_ext
  · rw [pullback.lift_fst, pullbackSymmetry_hom_comp_fst]
  · rw [pullback.lift_snd, pullbackSymmetry_hom_comp_snd]

/-- The symmetry of a fibre product is an isomorphism. -/
instance isIso_pullbackSwapMor : IsIso (pullbackSwapMor a b) :=
  pullbackSwapMor_eq a b ▸ inferInstance

/-- The symmetry of a fibre product followed by the structure morphism of `Y ×_S X` is the
structure morphism of `X ×_S Y`. -/
theorem pullbackSwapMor_comp :
    pullback.fst a b ≫ a = pullbackSwapMor a b ≫ (pullback.fst b a ≫ b) := by
  rw [← Category.assoc, pullback.lift_fst, pullback.condition]

/-- **The box product across the symmetry of a fibre product.** The box product `F ⊠ G` on
`X ×_S Y` is the inverse image along the symmetry of the box product `G ⊠ F` on `Y ×_S X`: the
braiding of the tensor product interchanges the two tensor factors, and the inverse image of a
box product along a pair of morphisms is the tensor product of the two inverse images. -/
def externalTensorProductSwapIso (F : X.Modules) (G : Y.Modules) :
    externalTensorProduct a b F G ≅
      (Scheme.Modules.pullback (pullbackSwapMor a b)).obj (externalTensorProduct b a G F) :=
  Stacks.SheafOfModules.TensorPresentations.tensorSheafSwap (pullback a b).toRingedSpace
      ((Scheme.Modules.pullback (pullback.fst a b)).obj F)
      ((Scheme.Modules.pullback (pullback.snd a b)).obj G) ≪≫
    (pullbackLift_externalTensorProductIso b a (pullback.snd a b) (pullback.fst a b)
      pullback.condition.symm G F).symm

end Swap

section

variable {X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S) (F : X.Modules) (G G' : Y.Modules)
  [F.IsQuasicoherent] [G.IsQuasicoherent] [G'.IsQuasicoherent] (l : ℕ)
  (E : DiffOp.GlobalOp G G')
  (hE : DiffOp.IsGlobalDiffOpOfOrder b.relativeStructureSheafMap l E)

/-- The box product `1 ⊠ E` of the identity with a differential operator, together with its order
bound read relative to the symmetry composed with the structure morphism of `Y ×_S X`. -/
def boxOpRightAux :
    {T : DiffOp.GlobalOp (externalTensorProduct a b F G) (externalTensorProduct a b F G') //
      DiffOp.IsGlobalDiffOpOfOrder
        (pullbackSwapMor a b ≫ (pullback.fst b a ≫ b)).relativeStructureSheafMap l T} :=
  globalDiffOpEquivGlobalOpCongr _ l (externalTensorProductSwapIso a b F G).symm
      (externalTensorProductSwapIso a b F G').symm
    (globalDiffOpEquivRestrictPullback (pullbackSwapMor a b) (pullback.fst b a ≫ b)
        (externalTensorProduct b a G F) (externalTensorProduct b a G' F) l
      (globalDiffOpEquivOfIso (pullbackSwapMor a b) (pullback.fst b a ≫ b)
          (externalTensorProduct b a G F) (externalTensorProduct b a G' F) l
        ⟨boxOpLeft b a G G' F l E hE,
          isGlobalDiffOpOfOrder_boxOpLeft_base b a G G' F l E hE⟩))

/-- **The box product `1 ⊠ E` of the identity with a differential operator.** For a differential
operator `E : G ⟶ G'` of order at most `l` on `Y/S` and a quasi-coherent `𝒪_X`-module `F`, the box
product `E ⊠ 1 : G ⊠ F ⟶ G' ⊠ F` on `Y ×_S X`, read through the identification of `F ⊠ G` with the
inverse image of `G ⊠ F` along the symmetry of the fibre product. -/
def boxOpRight :
    DiffOp.GlobalOp (externalTensorProduct a b F G) (externalTensorProduct a b F G') :=
  (boxOpRightAux a b F G G' l E hE).1

/-- **`1 ⊠ E` is a differential operator of order at most `l` on `X ×_S Y / S`.** -/
theorem isGlobalDiffOpOfOrder_boxOpRight :
    DiffOp.IsGlobalDiffOpOfOrder (pullback.fst a b ≫ a).relativeStructureSheafMap l
      (boxOpRight a b F G G' l E hE) :=
  (Iff.of_eq (congrArg (fun m ↦ DiffOp.IsGlobalDiffOpOfOrder
      (Scheme.Hom.relativeStructureSheafMap m) l (boxOpRight a b F G G' l E hE))
    (pullbackSwapMor_comp a b))).2 (boxOpRightAux a b F G G' l E hE).2

end

namespace FiniteOrderDifferentialOperatorCategory

variable {X Y S : Scheme.{u}} {a : X ⟶ S} {b : Y ⟶ S}

/-- **The box product of the identity with a finite-order differential operator.** For an object
`F` of the category of finite-order differential operators on `X/S` and a morphism `E : G ⟶ G'` of
the category on `Y/S`, the operator `1 ⊠ E : F ⊠ G ⟶ F ⊠ G'` of the category of finite-order
differential operators on `X ×_S Y / S`. -/
def boxHomRight (F : FiniteOrderDifferentialOperatorCategory a)
    {G G' : FiniteOrderDifferentialOperatorCategory b} (E : G ⟶ G') :
    boxProductObj F G ⟶ boxProductObj F G' :=
  ⟨boxOpRight a b F.module G.module G'.module E.2.choose E.1 E.2.choose_spec,
    E.2.choose, isGlobalDiffOpOfOrder_boxOpRight a b F.module G.module G'.module
      E.2.choose E.1 E.2.choose_spec⟩

/-- **The box product `D ⊠ E` of two finite-order differential operators.** For morphisms
`D : F ⟶ F'` of the category of finite-order differential operators on `X/S` and `E : G ⟶ G'` of
the category on `Y/S`, the composite `(1 ⊠ E) ∘ (D ⊠ 1) : F ⊠ G ⟶ F' ⊠ G'` of the category of
finite-order differential operators on `X ×_S Y / S`. -/
@[stacks 0G46 "the assignment on morphisms of the box product of the remark: for `D : F ⟶ F'` \
on `X/S` and `E : G ⟶ G'` on `Y/S` the operator `D ⊠ E = (1 ⊠ E) ∘ (D ⊠ 1)`, a morphism \
`F ⊠ G ⟶ F' ⊠ G'` of the category of finite-order differential operators on `X ×_S Y / S`. \
The FUNCTOR of the remark is not constructed HERE: `map_id`, `map_comp` and the bilinearity on \
morphisms are proved in `BoxProductFunctor`, and the affine description \
`(M, N) ↦ M ⊗_R N`, `(D, D') ↦ D ⊗ D'` in `BoxProductAffineDescription`"]
def boxHom {F F' : FiniteOrderDifferentialOperatorCategory a}
    {G G' : FiniteOrderDifferentialOperatorCategory b} (D : F ⟶ F') (E : G ⟶ G') :
    boxProductObj F G ⟶ boxProductObj F' G' :=
  boxHomLeft G D ≫ boxHomRight F' E

end FiniteOrderDifferentialOperatorCategory

end AlgebraicGeometry

end
