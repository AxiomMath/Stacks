module

public import Mathlib.Algebra.DirectSum.Ring
public import Mathlib.Algebra.GradedMulAction
public import Mathlib.Algebra.Module.GradedModule
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import StacksFrontier.Topology.Sheaves.Modules.InvertibleAndOperators.SectionRing
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerIntegerCoherence

/-!
# The graded ring and graded module structures on the sections of the twists

Let `𝒪` be a sheaf of commutative rings on a site with a terminal object and let `L` be an
invertible sheaf of `𝒪`-modules. The coherent multiplication of the integer tensor powers of
`L` makes the section ring `⨁ n : ℕ, Γ(L^{⊗ n})` a graded commutative ring and the section
module `⨁ j : ℤ, Γ(F ⊗ L^{⊗ j})` of a sheaf of modules `F` a graded module over it.

## Main definitions

* `Stacks.SheafOfModules.tensorSectionsAt` is the section of a tensor product of sheaves of
  modules determined by a pair of sections of the factors.
* `Stacks.SheafOfModules.sectionRingMul` multiplies two homogeneous sections of tensor powers.
* `Stacks.SheafOfModules.sectionModuleAction` acts by a homogeneous section of a tensor power
  on a homogeneous section of a twist.
* `Stacks.SheafOfModules.tensorPowerMulSectionAt` multiplies a section of `L^{⊗ n}` and a
  section of `L^{⊗ m}` over an arbitrary object, and
  `Stacks.SheafOfModules.tensorPowerMulHom` multiplies two morphisms `𝒪 ⟶ L^{⊗ n}`,
  `𝒪 ⟶ L^{⊗ m}`.
* `Stacks.SheafOfModules.twistActionHom` is multiplication of the twist `F ⊗ L^{⊗ j}` by a
  morphism `𝒪 ⟶ L^{⊗ n}`, as a morphism of sheaves, and
  `Stacks.SheafOfModules.globalSectionHom` is the morphism `𝒪 ⟶ M` determined by a global
  section of `M`.
* `Stacks.SheafOfModules.SectionRingStructure` and
  `Stacks.SheafOfModules.SectionModuleStructure` package a graded ring, resp. module,
  structure together with the requirement that it be the one above on homogeneous elements.

## Main results

* `Stacks.SheafOfModules.sectionRingStructure_exists`: the section ring carries a graded
  commutative ring structure whose homogeneous product is `sectionRingMul`.
* `Stacks.SheafOfModules.sectionModuleStructure_exists`: the section module carries a module
  structure over the section ring whose action on homogeneous elements is
  `sectionModuleAction`.
* `Stacks.SheafOfModules.tensorSections_leftUnitorAt`,
  `Stacks.SheafOfModules.tensorSections_rightUnitorAt`,
  `Stacks.SheafOfModules.tensorSections_braidingAt`,
  `Stacks.SheafOfModules.tensorSections_associatorAt` and
  `Stacks.SheafOfModules.tensorSections_tensorProductIsoAt` evaluate the coherence
  isomorphisms of the monoidal structure on such sections; they are the section-level
  calculus that homogeneous localization consumes.
* `Stacks.SheafOfModules.sectionRingGradingGradedRing` and
  `Stacks.SheafOfModules.sectionModuleGradedSMul` record that the homogeneous components of
  `StacksFrontier/Topology/Sheaves/Modules/InvertibleAndOperators/SectionRing.lean` are an internal
  grading for these structures, which is what homogeneous localization consumes.

## Implementation notes

A homogeneous product is transported from the coherent multiplication
`L^{⊗ n} ⊗ L^{⊗ m} ≅ L^{⊗ (n + m)}` of Tag 01CU along the pairing of global sections, so the
graded ring axioms are the coherence laws of that multiplication evaluated on sections. The
unit, associativity and commutativity laws hold on the nose only after reindexing the degree,
so each law is proved by transporting the corresponding identity along
`Stacks.SheafOfModules.TensorPower.tensorPowerReindex` and then cancelling the two
reindexings against each other.

The module axioms are proved not on sections directly but on the sheaf morphisms they induce:
`twistActionHom` is the action of a *global section* of `L^{⊗ n}`, i.e. a morphism from the
unit, as a morphism of sheaves, and the associativity and unit laws for the action are
equalities of such morphisms. Those are checked on pure tensors by `tensorSheaf_hom_ext`,
which is where the universal property of sheafification enters. Evaluating them back on
sections, through `globalSectionHom`, gives the laws for `sectionModuleAction`.

## References

* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite MonoidalCategory
open scoped DirectSum TensorProduct

universe v u w

namespace Stacks.SheafOfModules

attribute [local implicit_reducible] TensorSheafification.structureSheaf Tensor.sheafTensor

attribute [local instance] monoidalCategoryPresheafOfModules symmetricCategoryPresheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasTerminal C]
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

omit [HasTerminal C] in
/-- The unit of the sheafification adjunction is natural in the presheaf of modules: the
sheafification of a morphism, evaluated on the image of a section under the unit, is the image
under the unit of the value of the morphism on that section. -/
theorem toSheafify_app_map_obj
    {P Q : PresheafOfModules.{w} (TensorSheafification.structureSheaf O hO).obj}
    (f : P ⟶ Q) (U : Cᵒᵖ) (x : P.obj U) :
    (((TensorSheafification.sheafify O hO).map f).val.app U)
        ((TensorSheafification.toSheafify O hO P).app U x) =
      (TensorSheafification.toSheafify O hO Q).app U ((f.app U) x) :=
  (congrArg (fun k => (k.app U) x)
    ((TensorSheafification.sheafifyAdjunction O hO).unit.naturality f)).symm

omit [HasTerminal C] in
/-- The triangle identity of the sheafification adjunction, on sections: the counit undoes the
unit on the sections of a sheaf of modules. -/
theorem sheafifyCounit_toSheafify_app
    (M : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    (U : Cᵒᵖ) (x : M.val.obj U) :
    ((TensorSheafification.sheafifyAdjunction O hO).counit.app M).val.app U
      ((TensorSheafification.toSheafify O hO M.val).app U x) = x :=
  congrArg (fun f => (f.app U) x)
    ((TensorSheafification.sheafifyAdjunction O hO).right_triangle_components M)



section

omit [HasTerminal C]

/-- The section of the tensor product sheaf `F ⊗ G` over `U` determined by a section of `F`
and a section of `G` over `U`: the image of the pure tensor under the unit of the
sheafification adjunction. -/
noncomputable def tensorSectionsAt (U : Cᵒᵖ)
    (F G : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    (s : F.val.obj U) (t : G.val.obj U) :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O)
        (forget₂ CommRingCat RingCat) (hO)⟩).obj (F)).obj (G))).val.obj U :=
  (TensorSheafification.toSheafify O hO (F.val ⊗ G.val)).app U
    (s ⊗ₜ[(O.obj U)] t)

/-- The tensor product of two morphisms of sheaves of modules sends the section determined by
a pair of sections to the section determined by their images. -/
theorem tensorSections_tensorMapAt (U : Cᵒᵖ)
    (F F' G G' : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    (f : F ⟶ F') (g : G ⟶ G')
    (s : F.val.obj U) (t : G.val.obj U) :
    (((Invertible.tensorProductBifunctor O hO).map
      (X := (F, G)) (Y := (F', G')) (f, g)).val.app
      U)
      (tensorSectionsAt O hO U F G s t) =
        tensorSectionsAt O hO U F' G' (f.val.app U s)
          (g.val.app U t) := by
  show (((TensorSheafification.sheafify O hO).map (f.val ⊗ₘ g.val)).val.app U)
      ((TensorSheafification.toSheafify O hO (F.val ⊗ G.val)).app U (s ⊗ₜ t)) = _
  refine (toSheafify_app_map_obj (O := O) (hO := hO) (f := f.val ⊗ₘ g.val) U
    (s ⊗ₜ t)).trans ?_
  show (TensorSheafification.toSheafify O hO (F'.val ⊗ G'.val)).app U
      (((f.val ⊗ₘ g.val).app U) (s ⊗ₜ t)) =
    (TensorSheafification.toSheafify O hO (F'.val ⊗ G'.val)).app U
      ((f.val.app U s) ⊗ₜ (g.val.app U t))
  congr 1

/-- The left unitor sends the section determined by the unit section `1` of the structure sheaf
and a section `t` back to `t`. -/
theorem tensorSections_leftUnitorAt (U : Cᵒᵖ)
    (M : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    (t : M.val.obj U) :
    (((Invertible.tensorProductLeftUnitor O hO M).hom.val.app U)
      (tensorSectionsAt O hO U (SheafOfModules.unit (TensorSheafification.structureSheaf O hO)) M
        (1 : O.obj U) t)) = t := by
  show ((TensorSheafification.sheafifyAdjunction O hO).counit.app M).val.app U
      ((((TensorSheafification.sheafify O hO).map (λ_ M.val).hom).val.app U)
        ((TensorSheafification.toSheafify O hO
          (𝟙_ (PresheafOfModules.{w} (TensorSheafification.structureSheaf O hO).obj)
            ⊗ M.val)).app U
          ((1 : O.obj U) ⊗ₜ t))) = t
  refine Eq.trans (congrArg
    (fun y => ((TensorSheafification.sheafifyAdjunction O hO).counit.app M).val.app U y)
    (toSheafify_app_map_obj (O := O) (hO := hO) (f := (λ_ M.val).hom)
      U ((1 : O.obj U) ⊗ₜ t))) ?_
  refine Eq.trans (sheafifyCounit_toSheafify_app (O := O) (hO := hO) M U
    (((λ_ M.val).hom.app U) ((1 : O.obj U) ⊗ₜ t))) ?_
  let _i : CommRing ↑(((TensorSheafification.structureSheaf O hO).obj).obj U) :=
    inferInstanceAs (CommRing (O.obj U))
  show ((λ_ (M.val.obj U)).hom) (1 ⊗ₜ t) = t
  rw [ModuleCat.MonoidalCategory.leftUnitor_hom_apply]
  exact one_smul _ _

/-- The right unitor sends the section determined by a section `t` and the unit section `1` of
the structure sheaf back to `t`. -/
theorem tensorSections_rightUnitorAt (U : Cᵒᵖ)
    (M : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    (t : M.val.obj U) :
    (((Invertible.tensorProductRightUnitor O hO M).hom.val.app U)
      (tensorSectionsAt O hO U M (SheafOfModules.unit (TensorSheafification.structureSheaf O hO))
        t (1 : O.obj U))) = t := by
  unfold TensorSheafification.structureSheaf at *
  show ((TensorSheafification.sheafifyAdjunction O hO).counit.app M).val.app U
      ((((TensorSheafification.sheafify O hO).map (ρ_ M.val).hom).val.app U)
        ((TensorSheafification.toSheafify O hO
          (M.val
            ⊗ 𝟙_ (PresheafOfModules.{w} (TensorSheafification.structureSheaf O hO).obj))).app U
          (t ⊗ₜ (1 : O.obj U)))) = t
  refine Eq.trans (congrArg
    (fun y => ((TensorSheafification.sheafifyAdjunction O hO).counit.app M).val.app U y)
    (toSheafify_app_map_obj (O := O) (hO := hO) (f := (ρ_ M.val).hom)
      U (t ⊗ₜ (1 : O.obj U)))) ?_
  refine Eq.trans (sheafifyCounit_toSheafify_app (O := O) (hO := hO) M U
    (((ρ_ M.val).hom.app U) (t ⊗ₜ (1 : O.obj U)))) ?_
  let _i : CommRing ↑(((TensorSheafification.structureSheaf O hO).obj).obj U) :=
    inferInstanceAs (CommRing (O.obj U))
  show ((ρ_ (M.val.obj U)).hom) (t ⊗ₜ (1 : O.obj U)) = t
  rw [ModuleCat.MonoidalCategory.rightUnitor_hom_apply]
  exact one_smul _ _

/-- The braiding exchanges the two sections determining a section of a tensor product. -/
theorem tensorSections_braidingAt (U : Cᵒᵖ)
    (F G : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    (s : F.val.obj U) (t : G.val.obj U) :
    (((Invertible.tensorProductBraiding O hO F G).hom.val.app U)
      (tensorSectionsAt O hO U F G s t)) =
      tensorSectionsAt O hO U G F t s := by
  unfold TensorSheafification.structureSheaf at *
  let _i : CommRing ↑(((TensorSheafification.structureSheaf O hO).obj).obj U) :=
    inferInstanceAs (CommRing (O.obj U))
  have hβApp : (ConcreteCategory.hom ((β_ F.val G.val).hom.app U))
      (s ⊗ₜ t) = t ⊗ₜ s := by
    rw [PresheafOfModules.braiding_hom_app]
    exact ModuleCat.MonoidalCategory.braiding_hom_apply s t
  show (((TensorSheafification.sheafify O hO).map (β_ F.val G.val).hom).val.app
      U)
      ((TensorSheafification.toSheafify O hO (F.val ⊗ G.val)).app U (s ⊗ₜ t)) = _
  exact (toSheafify_app_map_obj (O := O) (hO := hO)
    (f := (β_ F.val G.val).hom) U (s ⊗ₜ t)).trans
    (congrArg (fun y => (TensorSheafification.toSheafify O hO (G.val ⊗ F.val)).app U y) hβApp)

/-- The associator reassociates the three sections determining a section of an iterated tensor
product. -/
theorem tensorSections_associatorAt (U : Cᵒᵖ)
    (F G H : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    (s : F.val.obj U) (t : G.val.obj U)
    (u : H.val.obj U) :
    (((Invertible.tensorProductAssociator O hO F G H).hom.val.app U)
      (tensorSectionsAt O hO U ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O,
          Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj (F)).obj
          (G))) H
        (tensorSectionsAt O hO U F G s t) u)) =
      tensorSectionsAt O hO U F ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O,
          Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj (G)).obj
          (H))) s
        (tensorSectionsAt O hO U G H t u) := by
  unfold TensorSheafification.structureSheaf at *
  let fLeft := TensorSheafification.toSheafify O hO (F.val ⊗ G.val) ▷ H.val
  let fRight := F.val ◁ TensorSheafification.toSheafify O hO (G.val ⊗ H.val)
  let _iL : IsIso ((TensorSheafification.sheafify O hO).map fLeft) :=
    TensorSheafification.isIso_sheafify_map_whiskerRight O hO
      (TensorSheafification.toSheafify O hO (F.val ⊗ G.val)) H.val
      (TensorSheafification.isIso_sheafify_map_toSheafify O hO (F.val ⊗ G.val))
  let _iR : IsIso ((TensorSheafification.sheafify O hO).map fRight) :=
    TensorSheafification.isIso_sheafify_map_whiskerLeft O hO F.val
      (TensorSheafification.toSheafify O hO (G.val ⊗ H.val))
      (TensorSheafification.isIso_sheafify_map_toSheafify O hO (G.val ⊗ H.val))
  let eLeft := asIso ((TensorSheafification.sheafify O hO).map fLeft)
  let eRight := asIso ((TensorSheafification.sheafify O hO).map fRight)
  let _i : CommRing ↑(((TensorSheafification.structureSheaf O hO).obj).obj U) :=
    inferInstanceAs (CommRing (O.obj U))
  let x : ((F.val ⊗ G.val) ⊗ H.val).obj U := (s ⊗ₜ t) ⊗ₜ u
  let y : ((((TensorSheafification.sheafify O hO).obj (F.val ⊗ G.val)).val ⊗ H.val).obj U) :=
      (TensorSheafification.toSheafify O hO (F.val ⊗ G.val)).app U (s ⊗ₜ t) ⊗ₜ u
  let z : (F.val ⊗ (G.val ⊗ H.val)).obj U := s ⊗ₜ (t ⊗ₜ u)
  let x' : (F.val ⊗ ((TensorSheafification.sheafify O hO).obj (G.val ⊗ H.val)).val).obj U := s ⊗ₜ
      (TensorSheafification.toSheafify O hO (G.val ⊗ H.val)).app U
        (t ⊗ₜ u)
  have hLeftMap : (eLeft.hom.val.app U)
      ((TensorSheafification.toSheafify O hO
        (((F.val ⊗ G.val) ⊗ H.val))).app U x) =
      (TensorSheafification.toSheafify O hO
        (((TensorSheafification.sheafify O hO).obj (F.val ⊗ G.val)).val ⊗ H.val)).app U y := by
    show (((TensorSheafification.sheafify O hO).map fLeft).val.app U)
        ((TensorSheafification.toSheafify O hO ((F.val ⊗ G.val) ⊗ H.val)).app U x) = _
    calc
      _ = (TensorSheafification.toSheafify O hO
          (((TensorSheafification.sheafify O hO).obj (F.val ⊗ G.val)).val ⊗ H.val)).app U
          ((fLeft.app U) x) :=
        toSheafify_app_map_obj (O := O) (hO := hO) (f := fLeft) U x
      _ = (TensorSheafification.toSheafify O hO
          (((TensorSheafification.sheafify O hO).obj (F.val ⊗ G.val)).val ⊗ H.val)).app U y := by
        rfl
  have hLeftInv : (eLeft.inv.val.app U)
      ((TensorSheafification.toSheafify O hO
        (((TensorSheafification.sheafify O hO).obj (F.val ⊗ G.val)).val ⊗ H.val)).app U y) =
      (TensorSheafification.toSheafify O hO ((F.val ⊗ G.val) ⊗ H.val)).app U x := by
    rw [← hLeftMap]
    show ((eLeft.hom ≫ eLeft.inv).val.app U)
      ((TensorSheafification.toSheafify O hO ((F.val ⊗ G.val) ⊗ H.val)).app U x) = _
    rw [eLeft.hom_inv_id]
    rfl
  have hAlphaApp : ((α_ F.val G.val H.val).hom.app U) x = z := by
    show ((CategoryTheory.MonoidalCategoryStruct.associator F.val G.val H.val).hom.app U) x = z
    rw [PresheafOfModules.associator_hom_app]
    exact ModuleCat.MonoidalCategory.associator_hom_apply s t u
  have hAlpha : (((TensorSheafification.sheafify O hO).map (α_ F.val G.val H.val).hom).val.app U)
      ((TensorSheafification.toSheafify O hO ((F.val ⊗ G.val) ⊗ H.val)).app U x) =
      (TensorSheafification.toSheafify O hO (F.val ⊗ (G.val ⊗ H.val))).app U z := by
    calc
      _ = (TensorSheafification.toSheafify O hO (F.val ⊗ (G.val ⊗ H.val))).app U
          ((α_ F.val G.val H.val).hom.app U x) :=
        toSheafify_app_map_obj (O := O) (hO := hO)
          (f := (α_ F.val G.val H.val).hom) U x
      _ = (TensorSheafification.toSheafify O hO (F.val ⊗ (G.val ⊗ H.val))).app U z := by
        rw [hAlphaApp]
  have hRightMap : (eRight.hom.val.app U)
      ((TensorSheafification.toSheafify O hO (F.val ⊗ (G.val ⊗ H.val))).app U z) =
      (TensorSheafification.toSheafify O hO
        (F.val ⊗ ((TensorSheafification.sheafify O hO).obj (G.val ⊗ H.val)).val)).app U x' := by
    show (((TensorSheafification.sheafify O hO).map fRight).val.app U)
        ((TensorSheafification.toSheafify O hO (F.val ⊗ (G.val ⊗ H.val))).app U z) = _
    calc
      _ = (TensorSheafification.toSheafify O hO
          (F.val ⊗ ((TensorSheafification.sheafify O hO).obj (G.val ⊗ H.val)).val)).app U
          ((fRight.app U) z) :=
        toSheafify_app_map_obj (O := O) (hO := hO) (f := fRight) U z
      _ = (TensorSheafification.toSheafify O hO
          (F.val ⊗ ((TensorSheafification.sheafify O hO).obj (G.val ⊗ H.val)).val)).app U x' := by
        rfl
  show (eRight.hom.val.app U)
      (((TensorSheafification.sheafify O hO).map (α_ F.val G.val H.val).hom).val.app U
        ((eLeft.inv.val.app U)
          ((TensorSheafification.toSheafify O hO
            (((TensorSheafification.sheafify O hO).obj (F.val ⊗ G.val)).val ⊗ H.val)).app U y))) =
    (TensorSheafification.toSheafify O hO
      (F.val ⊗ ((TensorSheafification.sheafify O hO).obj (G.val ⊗ H.val)).val)).app U x'
  rw [hLeftInv, hAlpha, ← hRightMap]

/-- The tensor product of two isomorphisms of sheaves of modules sends the section determined
by a pair of sections to the section determined by their images. -/
theorem tensorSections_tensorProductIsoAt (U : Cᵒᵖ)
    (F F' G G' : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    (e : F ≅ F') (f : G ≅ G')
    (s : F.val.obj U) (t : G.val.obj U) :
    (((Invertible.tensorProductIso O hO e f).hom.val.app U)
      (tensorSectionsAt O hO U F G s t)) =
      tensorSectionsAt O hO U F' G' (e.hom.val.app U s)
        (f.hom.val.app U t) :=
  tensorSections_tensorMapAt O hO U F F' G G' e.hom f.hom s t

/-- The product of a section of `L^{⊗ n}` and a section of `L^{⊗ m}` over an object `U`, a
section of `L^{⊗ (n + m)}`: pair them and apply the coherent multiplication of the integer
tensor powers. -/
public noncomputable def tensorPowerMulSectionAt (U : Cᵒᵖ)
    (L : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] (n m : ℤ)
    (s : (TensorPower.tensorPower O hO L n).val.obj U)
    (t : (TensorPower.tensorPower O hO L m).val.obj U) :
    (TensorPower.tensorPower O hO L (n + m)).val.obj U :=
  ((TensorPower.coherentMulIso O hO L n m).hom.val.app U)
    (tensorSectionsAt O hO U _ _ s t)

/-- **The product of sections of tensor powers is commutative**, up to the reindexing
comparison that swaps the two degrees.

This is the `private` form, usable only inside this module. The public form of the same identity,
which `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TwistActionLinear` and
`StacksFrontier.AlgebraicGeometry.TwistedCohomologyLocalization.DegreeZeroNumerators` use, is
`Stacks.SheafOfModules.tensorPowerMulSectionAt_comm` just below: a `private` name resolves across
modules only while the dependent oleans come from cache, and turns into `unknown identifier` on
the first forced re-elaboration anywhere in this module's dependent closure. -/
private theorem tensorPowerMulSection_commAt (U : Cᵒᵖ)
    (L : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] (n m : ℤ)
    (s : (TensorPower.tensorPower O hO L n).val.obj U)
    (t : (TensorPower.tensorPower O hO L m).val.obj U) :
    tensorPowerMulSectionAt O hO U L n m s t =
      ((TensorPower.tensorPowerReindex O hO L (Int.add_comm m n)).hom.val.app
        U) (tensorPowerMulSectionAt O hO U L m n t s) := by
  have h := congrArg Iso.hom (TensorPower.coherentMulIso_comm O hO L n m)
  have happ := congrArg (fun f => (f.val.app U) (tensorSectionsAt O hO U _ _ s t)) h
  change ((TensorPower.coherentMulIso O hO L n m).hom.val.app U)
      (tensorSectionsAt O hO U _ _ s t) =
    ((TensorPower.tensorPowerReindex O hO L (Int.add_comm m n)).hom.val.app U)
      (((TensorPower.coherentMulIso O hO L m n).hom.val.app U)
        (((Invertible.tensorProductBraiding O hO _ _).hom.val.app U)
          (tensorSectionsAt O hO U _ _ s t))) at happ
  rw [tensorSections_braidingAt O hO U _ _ s t] at happ
  simpa [tensorPowerMulSectionAt] using happ

/-- **The product of sections of tensor powers is commutative**, up to the reindexing
comparison that swaps the two degrees.

This is the public form of `Stacks.SheafOfModules.tensorPowerMulSection_commAt`, for the modules
that multiply sections of tensor powers outside this one. -/
alias tensorPowerMulSectionAt_comm := tensorPowerMulSection_commAt

/-- **The product of sections of tensor powers is associative**, up to the reindexing
comparison that moves the bracketing of the three degrees. -/
private theorem tensorPowerMulSection_assocAt (U : Cᵒᵖ)
    (L : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] (n m k : ℤ)
    (s : (TensorPower.tensorPower O hO L n).val.obj U)
    (t : (TensorPower.tensorPower O hO L m).val.obj U)
    (u : (TensorPower.tensorPower O hO L k).val.obj U) :
    tensorPowerMulSectionAt O hO U L (n + m) k
        (tensorPowerMulSectionAt O hO U L n m s t) u =
      ((TensorPower.tensorPowerReindex O hO L (Int.add_assoc n m k).symm).hom.val.app
        U)
        (tensorPowerMulSectionAt O hO U L n (m + k) s
          (tensorPowerMulSectionAt O hO U L m k t u)) := by
  let α := Invertible.tensorProductAssociator O hO
    (TensorPower.tensorPower O hO L n) (TensorPower.tensorPower O hO L m)
    (TensorPower.tensorPower O hO L k)
  let μ₁ := TensorPower.coherentMulIso O hO L n m
  let μ₂ := TensorPower.coherentMulIso O hO L (n + m) k
  let μ₃ := TensorPower.coherentMulIso O hO L m k
  let μ₄ := TensorPower.coherentMulIso O hO L n (m + k)
  let ρ := TensorPower.tensorPowerReindex O hO L (Int.add_assoc n m k).symm
  let S := tensorSectionsAt O hO U
    ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O)
        (forget₂ CommRingCat RingCat) (hO)⟩).obj ((TensorPower.tensorPower O hO L n))).obj
        ((TensorPower.tensorPower O hO L m)))) (TensorPower.tensorPower O hO L k)
    (tensorSectionsAt O hO U (TensorPower.tensorPower O hO L n)
      (TensorPower.tensorPower O hO L m) s t) u
  have h := congrArg Iso.hom
    (TensorPower.coherentMulIso_assoc O hO L n m k)
  have happ := congrArg (fun f => (f.val.app U) S) h
  change (μ₂.hom.val.app U)
      ((Invertible.tensorProductIso O hO μ₁ (Iso.refl _)).hom.val.app U S) =
    (ρ.hom.val.app U)
      ((μ₄.hom.val.app U)
        ((Invertible.tensorProductIso O hO (Iso.refl _) μ₃).hom.val.app U
          (α.hom.val.app U S))) at happ
  have hLeft := congrArg (fun x => (μ₂.hom.val.app U) x)
    (tensorSections_tensorProductIsoAt O hO U _ _ _ _ μ₁
      (Iso.refl (TensorPower.tensorPower O hO L k))
      (tensorSectionsAt O hO U (TensorPower.tensorPower O hO L n)
        (TensorPower.tensorPower O hO L m) s t) u)
  have hRight := (congrArg
    (fun x => ((Invertible.tensorProductIso O hO
      (Iso.refl (TensorPower.tensorPower O hO L n)) μ₃).hom.val.app U) x)
    (tensorSections_associatorAt O hO U (TensorPower.tensorPower O hO L n)
      (TensorPower.tensorPower O hO L m) (TensorPower.tensorPower O hO L k) s t u)).trans
    (tensorSections_tensorProductIsoAt O hO U _ _ _ _
      (Iso.refl (TensorPower.tensorPower O hO L n)) μ₃ s
      (tensorSectionsAt O hO U (TensorPower.tensorPower O hO L m)
        (TensorPower.tensorPower O hO L k) t u))
  exact hLeft.symm.trans (happ.trans
    (congrArg (fun x => (ρ.hom.val.app U) ((μ₄.hom.val.app U) x)) hRight))

private theorem tensorPowerReindex_hom_applyAt (U : Cᵒᵖ)
    (L : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] {a b : ℤ} (h : a = b)
    (x : (TensorPower.tensorPower O hO L a).val.obj U) :
    ((TensorPower.tensorPowerReindex O hO L h).hom.val.app U) x =
      Eq.mp (congrArg (fun i =>
        ((TensorPower.tensorPower O hO L i).val.obj U).carrier) h) x := by
  cases h
  rfl

end



/-- The canonical product of two homogeneous sections of tensor powers. -/
noncomputable def sectionRingMul
    (L : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] (n m : ℕ)
    (s : (TensorPower.tensorPower O hO L (n : ℤ)).val.obj (op (⊤_ C)))
    (t : (TensorPower.tensorPower O hO L (m : ℤ)).val.obj (op (⊤_ C))) :
    (TensorPower.tensorPower O hO L ((n + m : ℕ) : ℤ)).val.obj (op (⊤_ C)) :=
  ((TensorPower.coherentMulIso O hO L (n : ℤ) (m : ℤ) ≪≫
      TensorPower.tensorPowerReindex O hO L (Int.natCast_add n m).symm).hom).val.app
    (op (⊤_ C)) (tensorGlobalSection O hO _ _ s t)

private theorem sectionRingMul_add_left
    (L : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] (n m : ℕ)
    (s₁ s₂ : (TensorPower.tensorPower O hO L (n : ℤ)).val.obj (op (⊤_ C)))
    (t : (TensorPower.tensorPower O hO L (m : ℤ)).val.obj (op (⊤_ C))) :
    sectionRingMul O hO L n m (s₁ + s₂) t =
      sectionRingMul O hO L n m s₁ t + sectionRingMul O hO L n m s₂ t := by
  unfold sectionRingMul
  rw [tensorGlobalSection_add_left]
  exact map_add _ _ _

private theorem sectionRingMul_add_right
    (L : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] (n m : ℕ)
    (s : (TensorPower.tensorPower O hO L (n : ℤ)).val.obj (op (⊤_ C)))
    (t₁ t₂ : (TensorPower.tensorPower O hO L (m : ℤ)).val.obj (op (⊤_ C))) :
    sectionRingMul O hO L n m s (t₁ + t₂) =
      sectionRingMul O hO L n m s t₁ + sectionRingMul O hO L n m s t₂ := by
  unfold sectionRingMul
  rw [tensorGlobalSection_add_right]
  exact map_add _ _ _

private theorem sectionRingMul_zero_left
    (L : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] (n m : ℕ)
    (t : (TensorPower.tensorPower O hO L (m : ℤ)).val.obj (op (⊤_ C))) :
    sectionRingMul O hO L n m 0 t = 0 := by
  unfold sectionRingMul
  rw [tensorGlobalSection_zero_left]
  exact map_zero _

private theorem sectionRingMul_zero_right
    (L : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] (n m : ℕ)
    (s : (TensorPower.tensorPower O hO L (n : ℤ)).val.obj (op (⊤_ C))) :
    sectionRingMul O hO L n m s 0 = 0 := by
  unfold sectionRingMul
  rw [tensorGlobalSection_zero_right]
  exact map_zero _

/-- The action of a homogeneous section on a homogeneous twisted section. -/
noncomputable def sectionModuleAction
    (L F : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] (n : ℕ) (j : ℤ)
    (s : (TensorPower.tensorPower O hO L (n : ℤ)).val.obj (op (⊤_ C)))
    (t : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O)
        (forget₂ CommRingCat RingCat) (hO)⟩).obj (F)).obj
        ((TensorPower.tensorPower O hO L j)))).val.obj (op (⊤_ C))) :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O)
        (forget₂ CommRingCat RingCat) (hO)⟩).obj (F)).obj ((TensorPower.tensorPower O hO L
        ((n : ℤ) + j))))).val.obj (op (⊤_ C)) :=
  ((Invertible.tensorProductBraiding O hO _ _ ≪≫
      Invertible.tensorProductAssociator O hO F _ _ ≪≫
      Invertible.tensorProductIso O hO (Iso.refl F)
        (TensorPower.coherentMulIso O hO L j (n : ℤ)) ≪≫
      Invertible.tensorProductIso O hO (Iso.refl F)
        (TensorPower.tensorPowerReindex O hO L (Int.add_comm j (n : ℤ)))).hom).val.app
    (op (⊤_ C)) (tensorGlobalSection O hO _ _ s t)

private theorem sectionModuleAction_add_left
    (L F : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] (n : ℕ) (j : ℤ)
    (s₁ s₂ : (TensorPower.tensorPower O hO L (n : ℤ)).val.obj (op (⊤_ C)))
    (t : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O)
        (forget₂ CommRingCat RingCat) (hO)⟩).obj (F)).obj
        ((TensorPower.tensorPower O hO L j)))).val.obj (op (⊤_ C))) :
    sectionModuleAction O hO L F n j (s₁ + s₂) t =
      sectionModuleAction O hO L F n j s₁ t +
        sectionModuleAction O hO L F n j s₂ t := by
  unfold sectionModuleAction
  exact Eq.trans (DFunLike.congr_arg _ (tensorGlobalSection_add_left O hO _ _ s₁ s₂ t))
    (map_add _ _ _)

private theorem sectionModuleAction_add_right
    (L F : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] (n : ℕ) (j : ℤ)
    (s : (TensorPower.tensorPower O hO L (n : ℤ)).val.obj (op (⊤_ C)))
    (t₁ t₂ : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O)
        (forget₂ CommRingCat RingCat) (hO)⟩).obj (F)).obj
        ((TensorPower.tensorPower O hO L j)))).val.obj (op (⊤_ C))) :
    sectionModuleAction O hO L F n j s (t₁ + t₂) =
      sectionModuleAction O hO L F n j s t₁ +
        sectionModuleAction O hO L F n j s t₂ := by
  unfold sectionModuleAction
  exact Eq.trans (DFunLike.congr_arg _ (tensorGlobalSection_add_right O hO _ _ s t₁ t₂))
    (map_add _ _ _)

private theorem tensorProductIso_powerReindex_hom_app
    (F : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    (L : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] {i j : ℤ} (h : i = j)
    (x : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O)
        (forget₂ CommRingCat RingCat) (hO)⟩).obj (F)).obj
        ((TensorPower.tensorPower O hO L i)))).val.obj
      (op (⊤_ C))) :
    ((Invertible.tensorProductIso O hO (Iso.refl F)
      (TensorPower.tensorPowerReindex O hO L h)).hom.val.app (op (⊤_ C))) x =
        Eq.mp (congrArg (fun k => ↑(
          ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O)
              (forget₂ CommRingCat RingCat) (hO)⟩).obj (F)).obj
              ((TensorPower.tensorPower O hO L k)))).val.obj
            (op (⊤_ C))) ) h) x := by
  cases h
  exact congrArg (fun morphism => (morphism.val.app (op (⊤_ C))) x)
    ((Invertible.tensorProductBifunctor O hO).map_id (F, TensorPower.tensorPower O hO L i))

private theorem sectionRingMul_one_left
    (L : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] (n : ℕ)
    (t : (TensorPower.tensorPower O hO L (n : ℤ)).val.obj (op (⊤_ C))) :
    (((TensorPower.tensorPowerReindex O hO L
      (congrArg (fun x : ℕ => (x : ℤ)) (Nat.zero_add n))).hom.val.app
      (op (⊤_ C)))
      (sectionRingMul O hO L 0 n (1 : O.obj (op (⊤_ C))) t)) = t := by
  let U := op (⊤_ C)
  calc
    ((TensorPower.tensorPowerReindex O hO L (Int.zero_add (n : ℤ))).hom.val.app U)
        (sectionRingMul O hO L 0 n (1 : O.obj U) t) =
        ((Invertible.tensorProductLeftUnitor O hO
          (TensorPower.tensorPower O hO L (n : ℤ))).hom.val.app U)
          (tensorGlobalSection O hO
            (SheafOfModules.unit (TensorSheafification.structureSheaf O hO))
            (TensorPower.tensorPower O hO L (n : ℤ)) (1 : O.obj U) t) := by
      unfold sectionRingMul
      exact congrArg (fun f => (f.val.app U)
        (tensorGlobalSection O hO (SheafOfModules.unit (TensorSheafification.structureSheaf O hO))
          (TensorPower.tensorPower O hO L (n : ℤ)) (1 : O.obj U) t))
        (congrArg Iso.hom (TensorPower.coherentMulIso_zero_left O hO L (n : ℤ)))
    _ = t := tensorSections_leftUnitorAt O hO (op (⊤_ C)) _ t

private theorem sectionRingMul_one_right
    (L : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] (n : ℕ)
    (s : (TensorPower.tensorPower O hO L (n : ℤ)).val.obj (op (⊤_ C))) :
    (((TensorPower.tensorPowerReindex O hO L
      (congrArg (fun x : ℕ => (x : ℤ)) (Nat.add_zero n))).hom.val.app
      (op (⊤_ C)))
      (sectionRingMul O hO L n 0 s (1 : O.obj (op (⊤_ C))))) = s := by
  let U := op (⊤_ C)
  calc
    ((TensorPower.tensorPowerReindex O hO L (Int.add_zero (n : ℤ))).hom.val.app U)
        (sectionRingMul O hO L n 0 s (1 : O.obj U)) =
        ((Invertible.tensorProductRightUnitor O hO
          (TensorPower.tensorPower O hO L (n : ℤ))).hom.val.app U)
          (tensorGlobalSection O hO (TensorPower.tensorPower O hO L (n : ℤ))
            (SheafOfModules.unit (TensorSheafification.structureSheaf O hO)) s (1 : O.obj U)) := by
      unfold sectionRingMul
      exact congrArg (fun f => (f.val.app U)
        (tensorGlobalSection O hO (TensorPower.tensorPower O hO L (n : ℤ))
          (SheafOfModules.unit (TensorSheafification.structureSheaf O hO)) s (1 : O.obj U)))
        (congrArg Iso.hom (TensorPower.coherentMulIso_zero_right O hO L (n : ℤ)))
    _ = s := tensorSections_rightUnitorAt O hO (op (⊤_ C)) _ s

private theorem sectionRingMul_assoc
    (L : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] (n m k : ℕ)
    (s : (TensorPower.tensorPower O hO L (n : ℤ)).val.obj (op (⊤_ C)))
    (t : (TensorPower.tensorPower O hO L (m : ℤ)).val.obj (op (⊤_ C)))
    (u : (TensorPower.tensorPower O hO L (k : ℤ)).val.obj (op (⊤_ C))) :
    sectionRingMul O hO L (n + m) k (sectionRingMul O hO L n m s t) u =
      ((TensorPower.tensorPowerReindex O hO L
        (congrArg (fun x : ℕ => (x : ℤ)) (Nat.add_assoc n m k).symm)).hom.val.app
        (op (⊤_ C)))
        (sectionRingMul O hO L n (m + k) s (sectionRingMul O hO L m k t u)) :=
  tensorPowerMulSection_assocAt O hO (op (⊤_ C)) L (n : ℤ) (m : ℤ) (k : ℤ) s t u

/-- Elements of `A i` and `A j` are heterogeneously equal if one is the transport of the other
along `i = j`. -/
private theorem heq_of_eq_mp_symm {ι : Sort*} (A : ι → Sort*) {i j : ι} (h : i = j)
    {x : A i} {y : A j} (hxy : x = Eq.mp (congrArg A h.symm) y) : HEq x y := by
  cases h
  exact heq_of_eq hxy

@[instance_reducible]
private noncomputable def sectionRingGCommRing
    (L : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] :
    DirectSum.GCommRing
      (fun n : ℕ => (TensorPower.tensorPower O hO L (n : ℤ)).val.obj (op (⊤_ C))) := by
  let A := fun n : ℕ =>
    ((TensorPower.tensorPower O hO L (n : ℤ)).val.obj (op (⊤_ C))).carrier
  letI : AddCommMonoid ℕ := inferInstance
  let _i : CommRing ↑(((TensorSheafification.structureSheaf O hO).obj).obj (op (⊤_ C))) :=
    inferInstanceAs (CommRing (O.obj (op (⊤_ C))))
  letI : GradedMonoid.GOne
      (fun n : ℕ => (TensorPower.tensorPower O hO L (n : ℤ)).val.obj
        (op (⊤_ C))) := ⟨by
    change (SheafOfModules.unit (TensorSheafification.structureSheaf O hO)).val.obj
      (op (⊤_ C))
    exact (1 : O.obj (op (⊤_ C)))⟩
  letI : GradedMonoid.GMul
      (fun n : ℕ => (TensorPower.tensorPower O hO L (n : ℤ)).val.obj
        (op (⊤_ C))) := ⟨fun {n m} s t => sectionRingMul O hO L n m s t⟩
  refine {
    mul := fun {n m} s t => sectionRingMul O hO L n m s t
    mul_zero := ?_
    zero_mul := ?_
    mul_add := ?_
    add_mul := ?_
    one := (1 : O.obj (op (⊤_ C)))
    one_mul := ?_
    mul_one := ?_
    mul_assoc := ?_
    natCast := fun n => (show A 0 from (n : O.obj (op (⊤_ C))))
    natCast_zero := by norm_cast
    natCast_succ := by
      intro n
      change ((n + 1 : ℕ) : O.obj (op (⊤_ C))) =
        (n : O.obj (op (⊤_ C))) + 1
      norm_cast
    mul_comm := ?_
    intCast := fun z => (show A 0 from (z : O.obj (op (⊤_ C))))
    intCast_ofNat := by
      intro n
      change ((n : ℤ) : O.obj (op (⊤_ C))) = (n : O.obj (op (⊤_ C)))
      simp
    intCast_negSucc_ofNat := by
      intro n
      change ((Int.negSucc n : ℤ) : O.obj (op (⊤_ C))) =
        -((n + 1 : ℕ) : O.obj (op (⊤_ C)))
      simp
  }
  · intro n m s
    exact sectionRingMul_zero_right O hO L n m s
  · intro n m t
    exact sectionRingMul_zero_left O hO L n m t
  · intro n m s t₁ t₂
    exact sectionRingMul_add_right O hO L n m s t₁ t₂
  · intro n m s₁ s₂ t
    exact sectionRingMul_add_left O hO L n m s₁ s₂ t
  · intro ⟨n, s⟩
    apply Sigma.ext (Nat.zero_add n)
    have h := sectionRingMul_one_left O hO L n s
    rw [tensorPowerReindex_hom_applyAt] at h
    exact heq_of_cast_eq (congrArg A (Nat.zero_add n)) h
  · intro ⟨n, s⟩
    apply Sigma.ext (Nat.add_zero n)
    have h := sectionRingMul_one_right O hO L n s
    rw [tensorPowerReindex_hom_applyAt] at h
    exact heq_of_cast_eq (congrArg A (Nat.add_zero n)) h
  · intro ⟨n, s⟩ ⟨m, t⟩ ⟨k, u⟩
    apply Sigma.ext (Nat.add_assoc n m k)
    have h := sectionRingMul_assoc O hO L n m k s t u
    rw [tensorPowerReindex_hom_applyAt] at h
    exact heq_of_eq_mp_symm A (Nat.add_assoc n m k) h
  · intro ⟨n, s⟩ ⟨m, t⟩
    apply Sigma.ext (Nat.add_comm n m)
    -- The integer-degree braiding equality supplies the second-coordinate equality.
    have h := tensorPowerMulSection_commAt O hO (op (⊤_ C)) L (n : ℤ) (m : ℤ) s t
    rw [tensorPowerReindex_hom_applyAt] at h
    refine heq_of_eq_mp_symm A (Nat.add_comm n m) ?_
    exact h

/-- A graded ring structure whose homogeneous product is tensor multiplication. -/
structure SectionRingStructure
    (L : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] where
  /-- The graded commutative ring structure on the homogeneous summands. -/
  gradedRing : DirectSum.GCommRing
    (fun n : ℕ => (TensorPower.tensorPower O hO L (n : ℤ)).val.obj (op (⊤_ C)))
  /-- The homogeneous product of `gradedRing` is `sectionRingMul`. -/
  mul_eq :
    letI : DirectSum.GCommRing
      (fun n : ℕ => (TensorPower.tensorPower O hO L (n : ℤ)).val.obj (op (⊤_ C))) := gradedRing
    ∀ (n m : ℕ) (s : (TensorPower.tensorPower O hO L (n : ℤ)).val.obj (op (⊤_ C)))
      (t : (TensorPower.tensorPower O hO L (m : ℤ)).val.obj (op (⊤_ C))),
      GradedMonoid.GMul.mul
        (A := fun k : ℕ => (TensorPower.tensorPower O hO L (k : ℤ)).val.obj (op (⊤_ C)))
        s t = sectionRingMul O hO L n m s t
/-- There is a graded ring structure on the section ring whose homogeneous product is tensor
multiplication. -/
@[stacks 01CV "graded ring multiplication"]
theorem sectionRingStructure_exists
    (L : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] :
    Nonempty (SectionRingStructure O hO L) :=
  ⟨{ gradedRing := sectionRingGCommRing O hO L, mul_eq := fun _ _ _ _ => rfl }⟩

/-- A chosen graded ring structure on the section ring whose homogeneous product is tensor
multiplication. -/
noncomputable def chosenRingStructure
    (L : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] : SectionRingStructure O hO L :=
  Classical.choice (sectionRingStructure_exists O hO L)

/-- The graded commutative ring structure on the homogeneous summands of the section ring. -/
noncomputable instance sectionRingGradedRing
    (L : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] :
    DirectSum.GCommRing
      (fun n : ℕ => (TensorPower.tensorPower O hO L (n : ℤ)).val.obj (op (⊤_ C))) :=
  (chosenRingStructure O hO L).gradedRing



/-- The section ring is internally graded by its homogeneous summands. -/
noncomputable instance sectionRingGradingGradedRing
    (L : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] : GradedRing (sectionRingGrading O hO L) where
  toDecomposition := directSumComponentDecomposition _
  one_mem := ⟨_, (DirectSum.one_def _).symm⟩
  mul_mem := by
    intro n m s t hs ht
    obtain ⟨s, rfl⟩ := hs
    obtain ⟨t, rfl⟩ := ht
    exact ⟨_, (DirectSum.of_mul_of (A := fun k : ℕ =>
      (TensorPower.tensorPower O hO L (k : ℤ)).val.obj (op (⊤_ C))) s t).symm⟩

/-- A module structure whose action on homogeneous terms is tensor multiplication. -/
structure SectionModuleStructure
    (L F : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] where
  /-- The module structure of the section module over the section ring. -/
  moduleInst : Module (sectionRing O hO L) (sectionModule O hO L F)
  /-- The action of `moduleInst` on homogeneous terms is `sectionModuleAction`. -/
  smul_eq :
    letI : Module (sectionRing O hO L) (sectionModule O hO L F) := moduleInst
    ∀ (n : ℕ) (j : ℤ)
      (s : (TensorPower.tensorPower O hO L (n : ℤ)).val.obj (op (⊤_ C)))
      (t : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O)
          (forget₂ CommRingCat RingCat) (hO)⟩).obj (F)).obj
          ((TensorPower.tensorPower O hO L j)))).val.obj (op (⊤_ C))),
      (DirectSum.of _ n s : sectionRing O hO L) •
        (DirectSum.of _ j t : sectionModule O hO L F) =
      DirectSum.of _ ((n : ℤ) + j) (sectionModuleAction O hO L F n j s t)

section

omit [HasTerminal C]

private theorem tensorSheaf_hom_ext
    {F G H : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO)}
    {f g : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O)
        (forget₂ CommRingCat RingCat) (hO)⟩).obj (F)).obj (G)) ⟶ H}
    (h : ∀ (U : Cᵒᵖ) (s : F.val.obj U) (t : G.val.obj U),
      f.val.app U (tensorSectionsAt O hO U F G s t) =
        g.val.app U (tensorSectionsAt O hO U F G s t)) : f = g := by
  unfold TensorSheafification.structureSheaf at *
  apply ((TensorSheafification.sheafifyAdjunction O hO).homEquiv (F.val ⊗ G.val) H).injective
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change F.val.obj U ⊗[O.obj U] G.val.obj U at x
  induction x using TensorProduct.induction_on with
  | zero =>
      exact (map_zero (((TensorSheafification.sheafifyAdjunction O hO).homEquiv
        (F.val ⊗ G.val) H f).app U).hom).trans
        (map_zero (((TensorSheafification.sheafifyAdjunction O hO).homEquiv
          (F.val ⊗ G.val) H g).app U).hom).symm
  | tmul s t => exact h U s t
  | add x y hx hy =>
      exact ((((TensorSheafification.sheafifyAdjunction O hO).homEquiv
        (F.val ⊗ G.val) H f).app U).hom.map_add x y).trans
        ((congrArg₂ (· + ·) hx hy).trans
          ((((TensorSheafification.sheafifyAdjunction O hO).homEquiv
            (F.val ⊗ G.val) H g).app U).hom.map_add x y).symm)

/-- Insert a factor `A` on the left of `M`, along a morphism `O ⟶ A`: write `M` as `O ⊗ M` and
tensor the morphism on the right by `M`. -/
noncomputable def tensorInsertHom
    (A M : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    (s : SheafOfModules.unit (TensorSheafification.structureSheaf O hO) ⟶ A) :
    M ⟶ (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O)
        (forget₂ CommRingCat RingCat) (hO)⟩).obj (A)).obj (M)) :=
  (Invertible.tensorProductLeftUnitor O hO M).inv ≫
    (Invertible.tensorProductBifunctor O hO).map
      (X := (SheafOfModules.unit (TensorSheafification.structureSheaf O hO), M)) (Y := (A, M))
      (s, 𝟙 M)

/-- Inserting a factor sends a section to its pair with the value of the morphism on the unit
section. -/
private theorem tensorInsertHom_apply
    (A M : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    (s : SheafOfModules.unit (TensorSheafification.structureSheaf O hO) ⟶ A)
    (U : Cᵒᵖ) (x : M.val.obj U) :
    (tensorInsertHom O hO A M s).val.app U x =
      tensorSectionsAt O hO U A M (s.val.app U (1 : O.obj U)) x := by
  let unitorM := Invertible.tensorProductLeftUnitor O hO M
  let one := SheafOfModules.unit (TensorSheafification.structureSheaf O hO)
  have h := tensorSections_leftUnitorAt O hO U M x
  have hc : (unitorM.inv.val.app U) ((unitorM.hom.val.app U)
      (tensorSectionsAt O hO U one M (1 : O.obj U) x)) =
      tensorSectionsAt O hO U one M (1 : O.obj U) x :=
    congrArg (fun f => f.val.app U (tensorSectionsAt O hO U one M (1 : O.obj U) x))
      unitorM.hom_inv_id
  have hi : (unitorM.inv.val.app U) x = tensorSectionsAt O hO U one M (1 : O.obj U) x :=
    (congrArg (fun y => (unitorM.inv.val.app U) y) h).symm.trans hc
  exact (congrArg (fun y => ((Invertible.tensorProductBifunctor O hO).map
      (X := (one, M)) (Y := (A, M)) (s, 𝟙 M)).val.app U y) hi).trans
    (tensorSections_tensorMapAt O hO U one A M M s (𝟙 M) (1 : O.obj U) x)

/-- **Multiplication of the twist `F ⊗ L^{⊗ j}` by the morphism `s : O ⟶ L^{⊗ n}`**, as a
morphism `F ⊗ L^{⊗ j} ⟶ F ⊗ L^{⊗ (n + j)}`: insert the factor `L^{⊗ n}`, move it past `F` and
multiply it into `L^{⊗ j}`. -/
noncomputable def twistActionHom
    (L F : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] (n j : ℤ)
    (s : SheafOfModules.unit (TensorSheafification.structureSheaf O hO) ⟶
      TensorPower.tensorPower O hO L n) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O)
        (forget₂ CommRingCat RingCat) (hO)⟩).obj (F)).obj ((TensorPower.tensorPower O hO L j))) ⟶
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O)
          (forget₂ CommRingCat RingCat) (hO)⟩).obj (F)).obj ((TensorPower.tensorPower O hO L
          (n + j)))) :=
  tensorInsertHom O hO _ _ s ≫
    (Invertible.tensorProductBraiding O hO _ _ ≪≫
      Invertible.tensorProductAssociator O hO F _ _ ≪≫
      Invertible.tensorProductIso O hO (Iso.refl F)
        (TensorPower.coherentMulIso O hO L j n) ≪≫
      Invertible.tensorProductIso O hO (Iso.refl F)
        (TensorPower.tensorPowerReindex O hO L (Int.add_comm j n))).hom

/-- **Multiplication acts on sections by multiplying the tensor-power factor.** -/
theorem twistActionHom_pure
    (L F : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] (n j : ℤ)
    (s : SheafOfModules.unit (TensorSheafification.structureSheaf O hO) ⟶
      TensorPower.tensorPower O hO L n) (U : Cᵒᵖ)
    (x : F.val.obj U) (y : (TensorPower.tensorPower O hO L j).val.obj U) :
    (twistActionHom O hO L F n j s).val.app U
        (tensorSectionsAt O hO U _ _ x y) =
      tensorSectionsAt O hO U _ _ x
        (tensorPowerMulSectionAt O hO U L n j (s.val.app U (1 : O.obj U)) y) := by
  show (Invertible.tensorProductIso O hO (Iso.refl F)
      (TensorPower.tensorPowerReindex O hO L (Int.add_comm j n))).hom.val.app U
    ((Invertible.tensorProductIso O hO (Iso.refl F)
      (TensorPower.coherentMulIso O hO L j n)).hom.val.app U
    ((Invertible.tensorProductAssociator O hO F _ _).hom.val.app U
    ((Invertible.tensorProductBraiding O hO _ _).hom.val.app U
    ((tensorInsertHom O hO _ _ s).val.app U (tensorSectionsAt O hO U _ _ x y))))) = _
  let s₁ := s.val.app U (1 : O.obj U)
  let Lj := TensorPower.tensorPower O hO L j
  let Ln := TensorPower.tensorPower O hO L n
  let β := Invertible.tensorProductBraiding O hO Ln
    (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O)
      (forget₂ CommRingCat RingCat) (hO)⟩).obj F).obj Lj)
  let α := Invertible.tensorProductAssociator O hO F Lj Ln
  let μ := Invertible.tensorProductIso O hO (Iso.refl F) (TensorPower.coherentMulIso O hO L j n)
  let ρ := Invertible.tensorProductIso O hO (Iso.refl F)
    (TensorPower.tensorPowerReindex O hO L (Int.add_comm j n))
  have e₁ := tensorInsertHom_apply O hO Ln _ s U (tensorSectionsAt O hO U F Lj x y)
  have e₂ := tensorSections_braidingAt O hO U Ln _ s₁ (tensorSectionsAt O hO U F Lj x y)
  have e₃ := tensorSections_associatorAt O hO U F Lj Ln x y s₁
  have e₄ := tensorSections_tensorProductIsoAt O hO U F F _ _ (Iso.refl F)
    (TensorPower.coherentMulIso O hO L j n) x (tensorSectionsAt O hO U Lj Ln y s₁)
  have e₅ := tensorSections_tensorProductIsoAt O hO U F F _ _ (Iso.refl F)
    (TensorPower.tensorPowerReindex O hO L (Int.add_comm j n)) x
    (tensorPowerMulSectionAt O hO U L j n y s₁)
  have e₆ := congrArg (fun z => tensorSectionsAt O hO U F _ x z)
    (tensorPowerMulSection_commAt O hO U L n j s₁ y)
  have e₁₂ := (congrArg (fun z => (β.hom.val.app U) z) e₁).trans e₂
  have e₁₃ := (congrArg (fun z => (α.hom.val.app U) z) e₁₂).trans e₃
  have e₁₄ := (congrArg (fun z => (μ.hom.val.app U) z) e₁₃).trans e₄
  exact ((congrArg (fun z => (ρ.hom.val.app U) z) e₁₄).trans e₅).trans e₆.symm

/-- The product of two morphisms representing tensor powers, a morphism
`O ⟶ L^{⊗ (n + m)}`. -/
noncomputable def tensorPowerMulHom
    (L : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] (n m : ℤ)
    (s : SheafOfModules.unit (TensorSheafification.structureSheaf O hO) ⟶
      TensorPower.tensorPower O hO L n)
    (t : SheafOfModules.unit (TensorSheafification.structureSheaf O hO) ⟶
      TensorPower.tensorPower O hO L m) :
    SheafOfModules.unit (TensorSheafification.structureSheaf O hO) ⟶
      TensorPower.tensorPower O hO L (n + m) :=
  t ≫ tensorInsertHom O hO _ _ s ≫ (TensorPower.coherentMulIso O hO L n m).hom

/-- The value of a product of two morphisms on the unit section is the product of their
values. -/
theorem tensorPowerMulHom_apply
    (L : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] (n m : ℤ)
    (s : SheafOfModules.unit (TensorSheafification.structureSheaf O hO) ⟶
      TensorPower.tensorPower O hO L n)
    (t : SheafOfModules.unit (TensorSheafification.structureSheaf O hO) ⟶
      TensorPower.tensorPower O hO L m) (U : Cᵒᵖ) :
    (tensorPowerMulHom O hO L n m s t).val.app U (1 : O.obj U) =
      tensorPowerMulSectionAt O hO U L n m
        (s.val.app U (1 : O.obj U)) (t.val.app U (1 : O.obj U)) := by
  show (TensorPower.coherentMulIso O hO L n m).hom.val.app U
    ((tensorInsertHom O hO _ _ s).val.app U (t.val.app U (1 : O.obj U))) = _
  rw [tensorInsertHom_apply]
  rfl

/-- **Multiplying by a product of two sections is multiplying by each in turn**, up to the
reindexing comparison that moves the bracketing of the three degrees. -/
private theorem twistActionHom_assoc
    (L F : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] (n m j : ℤ)
    (s : SheafOfModules.unit (TensorSheafification.structureSheaf O hO) ⟶
      TensorPower.tensorPower O hO L n)
    (t : SheafOfModules.unit (TensorSheafification.structureSheaf O hO) ⟶
      TensorPower.tensorPower O hO L m) :
    twistActionHom O hO L F (n + m) j (tensorPowerMulHom O hO L n m s t) =
      twistActionHom O hO L F m j t ≫ twistActionHom O hO L F n (m + j) s ≫
        (Invertible.tensorProductIso O hO (Iso.refl F)
          (TensorPower.tensorPowerReindex O hO L (Int.add_assoc n m j).symm)).hom := by
  apply tensorSheaf_hom_ext O hO
  intro U x y
  show _ = (Invertible.tensorProductIso O hO (Iso.refl F)
    (TensorPower.tensorPowerReindex O hO L (Int.add_assoc n m j).symm)).hom.val.app U
    ((twistActionHom O hO L F n (m + j) s).val.app U
    ((twistActionHom O hO L F m j t).val.app U (tensorSectionsAt O hO U _ _ x y)))
  rw [twistActionHom_pure, twistActionHom_pure, twistActionHom_pure,
    tensorSections_tensorProductIsoAt, tensorPowerMulHom_apply,
    tensorPowerMulSection_assocAt]
  rfl

/-- The identity of the unit, with its codomain pinned as the zeroth tensor power. The two
are equal, but only by unfolding the integer iteration, so a bare `𝟙 _` is not type-correct
at the transparency at which the rewrites below check their motives. -/
private noncomputable def unitToPowerZero
    (L : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO)) [IsInvertible O hO L] :
    SheafOfModules.unit (TensorSheafification.structureSheaf O hO) ⟶
      TensorPower.tensorPower O hO L 0 :=
  𝟙 _

/-- **Multiplying by the unit section is the reindexing comparison** `L^{⊗ j} ≅ L^{⊗ (0 + j)}`
tensored with `F`. -/
private theorem twistActionHom_one
    (L F : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] (j : ℤ) :
    twistActionHom O hO L F 0 j (unitToPowerZero O hO L) =
      (Invertible.tensorProductIso O hO (Iso.refl F)
        (TensorPower.tensorPowerReindex O hO L (Int.zero_add j).symm)).hom := by
  apply tensorSheaf_hom_ext O hO
  intro U x y
  rw [twistActionHom_pure, tensorSections_tensorProductIsoAt]
  show tensorSectionsAt O hO U _ _ x
    (tensorPowerMulSectionAt O hO U L 0 j (1 : O.obj U) y) =
      tensorSectionsAt O hO U _ _ x
        ((TensorPower.tensorPowerReindex O hO L (Int.zero_add j).symm).hom.val.app U y)
  congr 1
  have h := congrArg (fun e => e.hom.val.app U
    (tensorSectionsAt O hO U _ _ (1 : O.obj U) y))
    (TensorPower.coherentMulIso_zero_left O hO L j)
  change (TensorPower.tensorPowerReindex O hO L (Int.zero_add j)).hom.val.app U
    (tensorPowerMulSectionAt O hO U L 0 j (1 : O.obj U) y) = _ at h
  replace h : (TensorPower.tensorPowerReindex O hO L (Int.zero_add j)).hom.val.app U
      (tensorPowerMulSectionAt O hO U L 0 j (1 : O.obj U) y) = y :=
    h.trans (tensorSections_leftUnitorAt O hO U (TensorPower.tensorPower O hO L j) y)
  rw [tensorPowerReindex_hom_applyAt] at h
  rw [tensorPowerReindex_hom_applyAt]
  exact eq_of_heq ((heq_of_cast_eq _ h).trans (cast_heq _ _).symm)

end


/-- The morphism `O ⟶ M` determined by a global section of `M`, that is by a section over the
terminal object: restrict it along the unique morphism to the terminal object. -/
noncomputable def globalSectionHom
    (M : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    (s : M.val.obj (op (⊤_ C))) :
    SheafOfModules.unit (TensorSheafification.structureSheaf O hO) ⟶ M :=
  M.unitHomEquiv.symm (M.val.sectionsMk
    (fun U => M.val.map (terminal.from U.unop).op s) (by
      intro U V f
      rw [← PresheafOfModules.map_comp_apply]
      rw [show (terminal.from U.unop).op ≫ f = (terminal.from V.unop).op from
        Subsingleton.elim _ _]))

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- The value of `globalSectionHom` on the unit section over the terminal object is the given
section. -/
theorem globalSectionHom_apply
    (M : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    (s : M.val.obj (op (⊤_ C))) :
    (globalSectionHom O hO M s).val.app (op (⊤_ C)) (1 : O.obj (op (⊤_ C))) = s := by
  have h := congrArg (fun x : M.sections => x.val (op (⊤_ C)))
    (M.unitHomEquiv.apply_symm_apply (M.val.sectionsMk
      (fun U => M.val.map (terminal.from U.unop).op s) (by
        intro U V f
        rw [← PresheafOfModules.map_comp_apply]
        rw [show (terminal.from U.unop).op ≫ f = (terminal.from V.unop).op from
          Subsingleton.elim _ _])))
  change (globalSectionHom O hO M s).val.app (op (⊤_ C)) (1 : O.obj (op (⊤_ C))) =
    M.val.map (terminal.from (⊤_ C)).op s at h
  rwa [show terminal.from (⊤_ C) = 𝟙 _ from Subsingleton.elim _ _, op_id,
    PresheafOfModules.map_id] at h

private noncomputable def twistActionSection
    (L F : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] (n j : ℤ)
    (s : (TensorPower.tensorPower O hO L n).val.obj (op (⊤_ C)))
    (t : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O)
        (forget₂ CommRingCat RingCat) (hO)⟩).obj (F)).obj
        ((TensorPower.tensorPower O hO L j)))).val.obj
      (op (⊤_ C))) :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O)
        (forget₂ CommRingCat RingCat) (hO)⟩).obj (F)).obj ((TensorPower.tensorPower O hO L
        (n + j))))).val.obj
      (op (⊤_ C)) :=
  ((Invertible.tensorProductBraiding O hO _ _ ≪≫
      Invertible.tensorProductAssociator O hO F _ _ ≪≫
      Invertible.tensorProductIso O hO (Iso.refl F)
        (TensorPower.coherentMulIso O hO L j n) ≪≫
      Invertible.tensorProductIso O hO (Iso.refl F)
        (TensorPower.tensorPowerReindex O hO L (Int.add_comm j n))).hom).val.app
    (op (⊤_ C)) (tensorGlobalSection O hO _ _ s t)

private theorem twistActionHom_apply
    (L F : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] (n j : ℤ)
    (s : SheafOfModules.unit (TensorSheafification.structureSheaf O hO) ⟶
      TensorPower.tensorPower O hO L n)
    (t : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O)
        (forget₂ CommRingCat RingCat) (hO)⟩).obj (F)).obj
        ((TensorPower.tensorPower O hO L j)))).val.obj
      (op (⊤_ C))) :
    (twistActionHom O hO L F n j s).val.app (op (⊤_ C)) t =
      twistActionSection O hO L F n j (s.val.app (op (⊤_ C)) (1 : O.obj (op (⊤_ C)))) t :=
  congrArg (fun z => ((Invertible.tensorProductBraiding O hO
      (TensorPower.tensorPower O hO L n)
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O)
        (forget₂ CommRingCat RingCat) (hO)⟩).obj F).obj (TensorPower.tensorPower O hO L j)) ≪≫
      Invertible.tensorProductAssociator O hO F _ _ ≪≫
      Invertible.tensorProductIso O hO (Iso.refl F)
        (TensorPower.coherentMulIso O hO L j n) ≪≫
      Invertible.tensorProductIso O hO (Iso.refl F)
        (TensorPower.tensorPowerReindex O hO L (Int.add_comm j n))).hom).val.app
      (op (⊤_ C)) z)
    (tensorInsertHom_apply O hO _ _ s (op (⊤_ C)) t)

private theorem twistActionSection_assoc
    (L F : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] (n m j : ℤ)
    (s : (TensorPower.tensorPower O hO L n).val.obj (op (⊤_ C)))
    (t : (TensorPower.tensorPower O hO L m).val.obj (op (⊤_ C)))
    (u : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O)
        (forget₂ CommRingCat RingCat) (hO)⟩).obj (F)).obj
        ((TensorPower.tensorPower O hO L j)))).val.obj
      (op (⊤_ C))) :
    twistActionSection O hO L F (n + m) j (tensorPowerMulSectionAt O hO (op (⊤_ C)) L n m s t) u =
      (Invertible.tensorProductIso O hO (Iso.refl F)
        (TensorPower.tensorPowerReindex O hO L (Int.add_assoc n m j).symm)).hom.val.app
          (op (⊤_ C))
        (twistActionSection O hO L F n (m + j) s (twistActionSection O hO L F m j t u)) := by
  have h := congrArg (fun f => f.val.app (op (⊤_ C)) u)
    (twistActionHom_assoc O hO L F n m j
      (globalSectionHom O hO _ s) (globalSectionHom O hO _ t))
  change _ = (Invertible.tensorProductIso O hO (Iso.refl F)
    (TensorPower.tensorPowerReindex O hO L (Int.add_assoc n m j).symm)).hom.val.app
      (op (⊤_ C))
    ((twistActionHom O hO L F n (m + j) (globalSectionHom O hO _ s)).val.app (op (⊤_ C))
      ((twistActionHom O hO L F m j (globalSectionHom O hO _ t)).val.app (op (⊤_ C)) u)) at h
  rwa [twistActionHom_apply, twistActionHom_apply, twistActionHom_apply,
    tensorPowerMulHom_apply, globalSectionHom_apply, globalSectionHom_apply] at h

private theorem twistActionSection_one
    (L F : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] (j : ℤ)
    (t : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O)
        (forget₂ CommRingCat RingCat) (hO)⟩).obj (F)).obj
        ((TensorPower.tensorPower O hO L j)))).val.obj
      (op (⊤_ C))) :
    twistActionSection O hO L F 0 j (1 : O.obj (op (⊤_ C))) t =
      (Invertible.tensorProductIso O hO (Iso.refl F)
        (TensorPower.tensorPowerReindex O hO L (Int.zero_add j).symm)).hom.val.app
          (op (⊤_ C)) t := by
  have h := congrArg (fun f => f.val.app (op (⊤_ C)) t) (twistActionHom_one O hO L F j)
  rwa [twistActionHom_apply] at h

/-- **The graded unit of the section ring is the unit section of the structure sheaf.** The
graded ring structure is chosen rather than constructed in place, so its unit has to be
identified by a calculation; the right unit law in degree `0` does it. -/
theorem sectionRingGradedOne_eq
    (L : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] :
    GradedMonoid.GOne.one (A := fun n : ℕ =>
      (TensorPower.tensorPower O hO L (n : ℤ)).val.obj (op (⊤_ C))) =
      (1 : O.obj (op (⊤_ C))) := by
  let A := fun n : ℕ => ((TensorPower.tensorPower O hO L (n : ℤ)).val.obj (op (⊤_ C))).carrier
  have h := GradedMonoid.GMonoid.one_mul (A := A) ⟨0, (1 : O.obj (op (⊤_ C)))⟩
  have hh : GradedMonoid.GMul.mul (A := A) (GradedMonoid.GOne.one (A := A))
      (show A 0 from (1 : O.obj (op (⊤_ C)))) = (1 : O.obj (op (⊤_ C))) :=
    eq_of_heq (Sigma.mk.inj h).2
  rw [(chosenRingStructure O hO L).mul_eq] at hh
  have hu := sectionRingMul_one_right O hO L 0 (GradedMonoid.GOne.one (A := A))
  change sectionRingMul O hO L 0 0 (GradedMonoid.GOne.one (A := A))
      (1 : O.obj (op (⊤_ C))) = GradedMonoid.GOne.one (A := A) at hu
  exact hu.symm.trans hh

/-- There is a module structure of the section module over the section ring whose action on
homogeneous terms is tensor multiplication. -/
@[stacks 01CV "graded module action"]
theorem sectionModuleStructure_exists
    (L F : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] :
    Nonempty (SectionModuleStructure O hO L F) := by
  let A : ℕ → Type w := fun n : ℕ => ((TensorPower.tensorPower O hO L (n : ℤ)).val.obj
    (op (⊤_ C))).carrier
  let M : ℤ → Type w := fun j : ℤ => (((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O,
      Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj (F)).obj
      ((TensorPower.tensorPower O hO L j)))).val.obj (op (⊤_ C))).carrier
  let _gring : DirectSum.GCommRing A := sectionRingGradedRing O hO L
  let _gmod : DirectSum.Gmodule A M := {
    smul := fun {n j} s t => sectionModuleAction O hO L F n j s t
    one_smul := by
      intro ⟨j, t⟩
      apply Sigma.ext (Int.zero_add j)
      show HEq (sectionModuleAction O hO L F 0 j
        (GradedMonoid.GOne.one (A := A)) t) t
      rw [sectionRingGradedOne_eq]
      have h := twistActionSection_one O hO L F j t
      rw [tensorProductIso_powerReindex_hom_app] at h
      exact (heq_of_eq h).trans (cast_heq _ _)
    mul_smul := by
      intro ⟨n, s⟩ ⟨m, t⟩ ⟨j, u⟩
      apply Sigma.ext (show ((n + m : ℕ) : ℤ) + j = (n : ℤ) + ((m : ℤ) + j) by omega)
      show HEq (sectionModuleAction O hO L F (n + m) j
        (GradedMonoid.GMul.mul (A := A) s t) u)
        (sectionModuleAction O hO L F n ((m : ℤ) + j) s
          (sectionModuleAction O hO L F m j t u))
      rw [(chosenRingStructure O hO L).mul_eq]
      have h := twistActionSection_assoc O hO L F (n : ℤ) (m : ℤ) j s t u
      rw [tensorProductIso_powerReindex_hom_app] at h
      exact (heq_of_eq h).trans (cast_heq _ _)
    smul_add := by
      intro n j s t u
      exact sectionModuleAction_add_right O hO L F n j s t u
    smul_zero := by
      intro n j s
      unfold sectionModuleAction
      exact Eq.trans (DFunLike.congr_arg _ (tensorGlobalSection_zero_right O hO _ _ s))
        (map_zero _)
    add_smul := by
      intro n j s t u
      exact sectionModuleAction_add_left O hO L F n j s t u
    zero_smul := by
      intro n j t
      unfold sectionModuleAction
      exact Eq.trans (DFunLike.congr_arg _ (tensorGlobalSection_zero_left O hO _ _ t))
        (map_zero _)
  }
  refine ⟨{ moduleInst := DirectSum.Gmodule.module A M, smul_eq := ?_ }⟩
  intro n j s t
  show DirectSum.of A n s • DirectSum.of M j t =
    DirectSum.of M ((n : ℤ) + j) (sectionModuleAction O hO L F n j s t)
  rw [DirectSum.Gmodule.of_smul_of A M s t]
  rfl

/-- A chosen module structure of the section module over the section ring whose action on
homogeneous terms is tensor multiplication. -/
noncomputable def chosenModuleStructure
    (L F : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] : SectionModuleStructure O hO L F :=
  Classical.choice (sectionModuleStructure_exists O hO L F)

/-- The module structure of the section module over the section ring. -/
noncomputable instance sectionModuleModule
    (L F : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] :
    Module (sectionRing O hO L) (sectionModule O hO L F) :=
  (chosenModuleStructure O hO L F).moduleInst


/-- The canonical action adds the degrees of homogeneous sections. -/
instance sectionModuleGradedSMul
    (L F : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] :
    SetLike.GradedSMul (sectionRingGrading O hO L) (sectionModuleGrading O hO L F) where
  smul_mem := by
    intro n j s t hs ht
    obtain ⟨s, rfl⟩ := hs
    obtain ⟨t, rfl⟩ := ht
    exact ⟨sectionModuleAction O hO L F n j s t,
      ((chosenModuleStructure O hO L F).smul_eq n j s t).symm⟩
end Stacks.SheafOfModules

end
