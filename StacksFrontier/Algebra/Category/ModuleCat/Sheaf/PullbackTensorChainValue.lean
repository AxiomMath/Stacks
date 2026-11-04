module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorChainSections

/-! # The chain of bijections of Tag 03EL on a pure tensor, at an arbitrary sheaf of values

Let `(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi and let `F`, `G` be
sheaves of `O_D`-modules. The two ends of the six-step chain
`Stacks.SheafOfModules.pullbackTensorHomEquiv` of **Tag 03EL** are evaluated by
`Stacks.SheafOfModules.pairingApp_pullbackTensorBottom` (steps 4, 5 and 6 traversed backwards
*from the identity*) and
`Stacks.SheafOfModules.pullbackTensorStep2_symm_step3_symm_val_app_unit_tmul` (steps 2 and 3
traversed backwards from an arbitrary pairing). Here they are joined, at an arbitrary sheaf of
values `N` and an arbitrary `k : f^*F ⊗_{O_C} f^*G ⟶ N`.

The result, `Stacks.SheafOfModules.pullbackTensorStep2to6_symm_val_app_unit_tmul`, is the value
formula for **the local sections of the adjoint transpose of the comparison of Tag 03EL followed by
`k`** — the morphism `F ⊗_{O_D} G ⟶ f_*N` that the last five steps of the chain produce from `k`,
read on the sheafification-unit image of a pure tensor `a ⊗ₜ r`. Steps 2 to 6 are what the adjoint
transpose consists of, step 1 having been cancelled by the transposition itself
(`Stacks.Sheaves.DerivedPullback.pullbackTensorAdjTranspose_eq`).

## Main results

* `Stacks.SheafOfModules.pullbackTensorStep4_symm_bottom_comp`: step 4 of the chain, traversed
  backwards at `Stacks.SheafOfModules.pullbackTensorBottomHom` composed with `k`, is the pairing at
  the identity composed with `k`.
* `Stacks.SheafOfModules.pullbackTensorStep2to6_symm_val_app_unit_tmul`: **steps 2 to 6 of the
  chain of Tag 03EL, traversed backwards from `k`, on the sheafification-unit image of a pure
  tensor.** The pair `(a, r)` is carried through the unit of `f⁻¹ ⊣ f_*` and then through the
  direct image of the product comparison of `f⁻¹` followed by that pairing.

Those two together are a complete description of the last five steps of the chain on a pure tensor:
the pairing appearing in the second is the one the first identifies, and its own value on a pair of
local sections of the inverse images is
`Stacks.SheafOfModules.pairingApp_pullbackTensorBottom` — the pure tensor of their images under the
unit of extension of scalars, with no scalar left over — followed by `k`, by
`Stacks.SheafOfModules.pairingApp_comp`.

## Implementation notes

**Why the topos unit stays.** The direct image of a sheaf has no description on local sections for
an abstract `CategoryTheory.Sheaf.MorphismOfTopoi`, and neither has the inverse image, so the unit
of `f⁻¹ ⊣ f_*` cannot be removed from the formula and the morphism inside `f_*` cannot be
evaluated: the value formula is the pair `(a, r)` pushed through the unit and then through the
direct image of a morphism upstairs, as in Tag 03D3. For a site-presented morphism of topoi the
direct image *can* be stripped, by
`AlgebraicGeometry.RingedSite.sectionsFunctor_map_pushforward_map`.

**No name for the pairing, and no written-out subtype.** The pairing is written out in both
statements rather than given a name: declaring it asks for its type — a subtype of a hom-set
between underlying sheaves of sets of restrictions of scalars, at the *concrete* tensor product
sheaf `Stacks.SheafOfModules.pullbackTensorTarget` — to be elaborated from scratch, and that
exhausts the heartbeat budget at `whnf` before the declaration has a body. Written as an anonymous
constructor on the right-hand side of an equation whose left-hand side is a step of the chain, the
type is propagated from the step and never elaborated on its own.

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 03D3](https://stacks.math.columbia.edu/tag/03D3)
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
-/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry CategoryTheory.Sheaf
open AlgebraicGeometry.SheafOfModules Stacks.Sheaves.RingedToposModules
open Stacks.PresheafOfModules.ChangeOfRings
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open scoped TensorProduct

universe w v u w' v' u'

namespace Stacks.SheafOfModules

section ChainValue

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  (f : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)
  (F G : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
  (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

omit [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] in
/-- **Step 4 of the chain of Tag 03EL, traversed backwards at the bottom of the chain composed
with `k`, is the pairing at the identity composed with `k`.** -/
lemma pullbackTensorStep4_symm_bottom_comp (k : pullbackTensorTarget f F G ⟶ N) :
    (pullbackTensorStep4 f F G N).symm
        (pullbackTensorBottomHom f F G ≫
          (SheafOfModules.restrictScalars f.fSharpInverseImage).map k) =
      ⟨((pullbackTensorStep4 f F G (pullbackTensorTarget f F G)).symm
              (pullbackTensorBottomHom f F G)).1 ≫
            (moduleSheafFunctor
                (inverseImageRingSheaf f.toToposHom
                  (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map
              ((SheafOfModules.restrictScalars f.fSharpInverseImage).map k),
        ((pullbackTensorStep4 f F G (pullbackTensorTarget f F G)).symm
              (pullbackTensorBottomHom f F G)).2.comp
          ((SheafOfModules.restrictScalars f.fSharpInverseImage).map k)⟩ := by
  refine (Equiv.symm_apply_eq _).mpr ?_
  refine Eq.trans ?_ (pullbackTensorStep4_naturality f F G
    ((pullbackTensorStep4 f F G (pullbackTensorTarget f F G)).symm
      (pullbackTensorBottomHom f F G)) k).symm
  exact congrArg
    (fun m ↦ m ≫ (SheafOfModules.restrictScalars f.fSharpInverseImage).map k)
    (Equiv.apply_symm_apply (pullbackTensorStep4 f F G (pullbackTensorTarget f F G))
      (pullbackTensorBottomHom f F G)).symm

/-- **Steps 2 to 6 of the chain of Tag 03EL, traversed backwards from `k`, on the
sheafification-unit image of a pure tensor.**

The last five steps of the chain carry `k : f^*F ⊗_{O_C} f^*G ⟶ N` to a morphism
`F ⊗_{O_D} G ⟶ f_*N`, and that morphism carries the unit image of `a ⊗ₜ r` to the pair `(a, r)`
pushed through the unit of `f⁻¹ ⊣ f_*` and then through the direct image of the product comparison
of `f⁻¹` followed by the pairing at the bottom of the chain composed with `k`. -/
theorem pullbackTensorStep2to6_symm_val_app_unit_tmul
    (k : pullbackTensorTarget f F G ⟶ N) (U : Y.Cᵒᵖ) (a : F.val.obj U) (r : G.val.obj U) :
    ((pullbackTensorStep2 f F G N).symm ((pullbackTensorStep3 f F G N).symm
            ((pullbackTensorStep4 f F G N).symm ((pullbackTensorStep5 f F G N).symm
              ((pullbackTensorStep6 f F G N).symm k))))).val.app U
        (((PresheafOfModules.sheafificationAdjunction
            (R := commRingSheaf Y.J Y.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property)
              (𝟙 _)).unit.app
            (F.val ⊗ G.val)).app U (a ⊗ₜ[(ringPresheaf Y.O.obj).obj U] r)) =
      (Sheaf.sectionsFunctor Y.J U).map
          (f.toToposHom.pushforward.map
            (prodComparison f.toToposHom.inverseImage
                (moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F)
                (moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G) ≫
              ((pullbackTensorStep4 f F G (pullbackTensorTarget f F G)).symm
                  (pullbackTensorBottomHom f F G)).1 ≫
                (moduleSheafFunctor
                    (inverseImageRingSheaf f.toToposHom
                      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map
                  ((SheafOfModules.restrictScalars f.fSharpInverseImage).map k)))
        ((Sheaf.sectionsFunctor Y.J U).map
          (f.toToposHom.adj.unit.app
            (moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F ⨯
              moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G))
          (Functor.prodObjMk a r)) := by
  have h6 : (pullbackTensorStep6 f F G N).symm k =
      (pullbackTensorStep6 f F G (pullbackTensorTarget f F G)).symm
        (𝟙 (pullbackTensorTarget f F G)) ≫ k := by
    show _ ≫ k = (_ ≫ 𝟙 _) ≫ k
    exact congrArg (fun m ↦ m ≫ k) (Category.comp_id _).symm
  have h5 : (pullbackTensorStep5 f F G N).symm ((pullbackTensorStep6 f F G N).symm k) =
      pullbackTensorBottomHom f F G ≫
        (SheafOfModules.restrictScalars f.fSharpInverseImage).map k := by
    rw [h6]
    exact (extendRestrictScalarsAdjunction X.J (fSharpCommRing f)
      (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property).homEquiv_naturality_right _ k
  rw [h5, pullbackTensorStep4_symm_bottom_comp]
  exact pullbackTensorStep2_symm_step3_symm_val_app_unit_tmul f F G N _ U a r

end ChainValue

end Stacks.SheafOfModules

end
