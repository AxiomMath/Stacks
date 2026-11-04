module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackModulesOfIsoStructureMap
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorToposCompBilinear
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The base change of bilinear pairings of Tag 03EL, evaluated forwards

Let `f` be a morphism of ringed topoi. This file computes the value of the base change of bilinear
pairings `Stacks.SheafOfModules.pullbackTensorBilinEquiv`,
`Bilin_{O_D}(F × G, f_*N) ≃ Bilin_{O_C}(f^*F × f^*G, N)`, at an arbitrary pairing `b` over `O_D`.

## Main results

* `Stacks.SheafOfModules.pullbackTensorStep3_apply_coe`: step 3 of the chain of Tag 03EL carries a
  pairing `b` over `O_D` to the inverse product comparison of `f⁻¹`, the inverse image of `b`, and
  the counit of `f⁻¹ ⊣ f_*`.
* `Stacks.SheafOfModules.pullbackTensorStep3_apply_coe_eq_prodMap_unit_comp`: the pairing produced
  by step 3 is the base change of `b` precomposed, in each variable, with the unit
  `ε : f⁻¹F ⟶ (f^*F)|` of the extension-restriction adjunction of Tag 03CZ.
* `Stacks.SheafOfModules.pullbackTensorBilinEquiv_apply_coe`: when the structure map of `f` is
  invertible, the base change of `b` is the composite

  `f^*F ⨯ f^*G ⟶ f⁻¹F ⨯ f⁻¹G ⟶ f⁻¹(F ⨯ G) ⟶ f⁻¹(f_*N) ⟶ N`

  of the two inverse units, the inverse product comparison of `f⁻¹`, the inverse image of `b`, and
  the counit of `f⁻¹ ⊣ f_*`.

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 03D3](https://stacks.math.columbia.edu/tag/03D3)
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 08PA](https://stacks.math.columbia.edu/tag/08PA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CategoryTheory.Sheaf
open AlgebraicGeometry.SheafOfModules Stacks.Sheaves.RingedToposModules
open Stacks.Sheaves.ToposPushforward
open Stacks.PresheafOfModules.ChangeOfRings

namespace Stacks.SheafOfModules

/-- If `u = prod.map a b ≫ v` with `a` and `b` isomorphisms, then
`v = prod.map (inv a) (inv b) ≫ u`. -/
theorem eq_prodMap_inv_comp {C : Type*} [Category C] {A B A' B' T : C}
    [HasBinaryProduct A B] [HasBinaryProduct A' B'] (a : A ⟶ A') (b : B ⟶ B')
    [IsIso a] [IsIso b] (u : A ⨯ B ⟶ T) (v : A' ⨯ B' ⟶ T) (h : u = prod.map a b ≫ v) :
    v = prod.map (inv a) (inv b) ≫ u := by
  rw [h, ← Category.assoc, prod.map_map, IsIso.inv_hom_id, IsIso.inv_hom_id, prod.map_id_id,
    Category.id_comp]

/-- If the left adjoint of an adjunction is isomorphic to a fully faithful functor, then each
component of the unit of the adjunction is an isomorphism. -/
@[sga "4 I 5.6" "ii⇒iii",
  sga "4 I 6.4" "more general",
  sga "4 IV 4.3.5" "Forward direction",
  sga "4 Vbis 2.2.5" "partial",
  sga "4 Vbis 2.4.9" "partial"]
theorem isIso_unit_app_of_isoFullyFaithful {C D : Type*} [Category C] [Category D]
    {L L' : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (e : L' ≅ L) (hfull : L'.Full)
    (hfaithful : L'.Faithful) (P : C) : IsIso (adj.unit.app P) :=
  let := hfull
  let := hfaithful
  let : L.Full := Functor.Full.of_iso e
  let : L.Faithful := Functor.Faithful.of_iso e
  inferInstance

section Value

universe w w' v u v' u'

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

omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] in
/-- Step 3 of the chain of Tag 03EL carries a pairing `b` over `O_D` into `f_*N` to the inverse
product comparison of `f⁻¹`, followed by the inverse image of `b`, followed by the counit of
`f⁻¹ ⊣ f_*`. -/
theorem pullbackTensorStep3_apply_coe
    (b : { q : moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F ⨯
          moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G ⟶
          moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ((pushforwardModules f).obj N) //
        IsBilinearPairing (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) q }) :
    (pullbackTensorStep3 f F G N b).1 =
      (PreservesLimitPair.iso f.toToposHom.inverseImage
            (moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F)
            (moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G)).inv ≫
        f.toToposHom.inverseImage.map b.1 ≫
          f.toToposHom.adj.counit.app
            (moduleSheaf (inverseImageRingSheaf f.toToposHom
                (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
              ((SheafOfModules.restrictScalars f.fSharpInverseImage).obj N)) :=
  inverseImageBilinearEquiv_symm_apply_coe_eq_comp_counit f.toToposHom
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F G
    ((SheafOfModules.restrictScalars f.fSharpInverseImage).obj N) b

omit [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] in
/-- For an arbitrary pairing `b` over `O_D` into `f_*N`, the pairing of the inverse images that
step 3 produces is the base change of `b` precomposed, in each variable, with the unit
`ε : f⁻¹F ⟶ (f^*F)|` of the extension-restriction adjunction of Tag 03CZ. -/
theorem pullbackTensorStep3_apply_coe_eq_prodMap_unit_comp
    (b : { q : moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F ⨯
          moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G ⟶
          moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ((pushforwardModules f).obj N) //
        IsBilinearPairing (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) q }) :
    (pullbackTensorStep3 f F G N b).1 =
      prod.map
          ((moduleSheafFunctor
              (commRingSheaf X.J (inverseImageStructureCommRing f)
                (isSheaf_inverseImageStructureCommRing f))).map
            ((pullbackExtendAdj f).unit.app
              ((inverseImageModules f.toToposHom
                (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F)))
          ((moduleSheafFunctor
              (commRingSheaf X.J (inverseImageStructureCommRing f)
                (isSheaf_inverseImageStructureCommRing f))).map
            ((pullbackExtendAdj f).unit.app
              ((inverseImageModules f.toToposHom
                (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G))) ≫
        (pullbackTensorBilinEquiv f F G N b).1 :=
  have hsplit : pullbackTensorBilinEquiv f F G N b =
      pullbackTensorExtendBilinEquiv f F G N (pullbackTensorStep3 f F G N b) :=
    congrArg (fun e ↦ e b) (pullbackTensorBilinEquiv_eq f F G N)
  (congrArg (fun z ↦ z.1)
        ((pullbackTensorExtendBilinEquiv f F G N).symm_apply_apply
          (pullbackTensorStep3 f F G N b)).symm).trans
    ((pullbackTensorExtendBilinEquiv_symm_apply_coe f F G N
          (pullbackTensorExtendBilinEquiv f F G N (pullbackTensorStep3 f F G N b))).trans
      (congrArg
        (fun z ↦ prod.map
              ((moduleSheafFunctor
                  (commRingSheaf X.J (inverseImageStructureCommRing f)
                    (isSheaf_inverseImageStructureCommRing f))).map
                ((pullbackExtendAdj f).unit.app
                  ((inverseImageModules f.toToposHom
                    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F)))
              ((moduleSheafFunctor
                  (commRingSheaf X.J (inverseImageStructureCommRing f)
                    (isSheaf_inverseImageStructureCommRing f))).map
                ((pullbackExtendAdj f).unit.app
                  ((inverseImageModules f.toToposHom
                    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G))) ≫ z.1)
        hsplit.symm))

omit [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] in
/-- For an arbitrary pairing `b` over `O_D` into `f_*N`, the base change of `b` precomposed in each
variable with the unit `ε : f⁻¹F ⟶ (f^*F)|` of Tag 03CZ is the inverse product comparison of
`f⁻¹`, followed by the inverse image of `b`, followed by the counit of `f⁻¹ ⊣ f_*`. -/
theorem prodMap_unit_comp_pullbackTensorBilinEquiv_apply_coe
    (b : { q : moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F ⨯
          moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G ⟶
          moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ((pushforwardModules f).obj N) //
        IsBilinearPairing (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) q }) :
    prod.map
          ((moduleSheafFunctor
              (commRingSheaf X.J (inverseImageStructureCommRing f)
                (isSheaf_inverseImageStructureCommRing f))).map
            ((pullbackExtendAdj f).unit.app
              ((inverseImageModules f.toToposHom
                (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F)))
          ((moduleSheafFunctor
              (commRingSheaf X.J (inverseImageStructureCommRing f)
                (isSheaf_inverseImageStructureCommRing f))).map
            ((pullbackExtendAdj f).unit.app
              ((inverseImageModules f.toToposHom
                (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G))) ≫
        (pullbackTensorBilinEquiv f F G N b).1 =
      (PreservesLimitPair.iso f.toToposHom.inverseImage
            (moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F)
            (moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G)).inv ≫
        f.toToposHom.inverseImage.map b.1 ≫
          f.toToposHom.adj.counit.app
            (moduleSheaf (inverseImageRingSheaf f.toToposHom
                (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
              ((SheafOfModules.restrictScalars f.fSharpInverseImage).obj N)) :=
  (pullbackTensorStep3_apply_coe_eq_prodMap_unit_comp f F G N b).symm.trans
    (pullbackTensorStep3_apply_coe f F G N b)

/-- If the structure map of `f` is invertible, each component of the unit of the
extension-restriction adjunction of Tag 03CZ is an isomorphism. -/
instance isIso_pullbackExtendAdj_unit_app [IsIso f.fSharpInverseImage]
    (P : SheafOfModules.{w} (inverseImageRingSheaf f.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :
    IsIso ((pullbackExtendAdj f).unit.app P) :=
  isIso_unit_app_of_isoFullyFaithful (pullbackExtendAdj f)
    f.extendScalarsFSharpIsoRestrictScalarsOfIsIso.symm
    (Equivalence.full_functor (Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso
      (asIso f.fSharpInverseImage)))
    (Equivalence.faithful_functor (Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso
      (asIso f.fSharpInverseImage))) P


omit [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] in
/-- If the structure map of `f` is invertible, the base change of a pairing `b` over `O_D` into
`f_*N` is the composite

`f^*F ⨯ f^*G ⟶ f⁻¹F ⨯ f⁻¹G ⟶ f⁻¹(F ⨯ G) ⟶ f⁻¹(f_*N) ⟶ N`

of the inverses of the two units of Tag 03CZ, the inverse product comparison of `f⁻¹`, the inverse
image of `b`, and the counit of `f⁻¹ ⊣ f_*`. -/
theorem pullbackTensorBilinEquiv_apply_coe [IsIso f.fSharpInverseImage]
    (b : { q : moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F ⨯
          moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G ⟶
          moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ((pushforwardModules f).obj N) //
        IsBilinearPairing (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) q }) :
    (pullbackTensorBilinEquiv f F G N b).1 =
      prod.map
          (inv ((moduleSheafFunctor
              (commRingSheaf X.J (inverseImageStructureCommRing f)
                (isSheaf_inverseImageStructureCommRing f))).map
            ((pullbackExtendAdj f).unit.app
              ((inverseImageModules f.toToposHom
                (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F))))
          (inv ((moduleSheafFunctor
              (commRingSheaf X.J (inverseImageStructureCommRing f)
                (isSheaf_inverseImageStructureCommRing f))).map
            ((pullbackExtendAdj f).unit.app
              ((inverseImageModules f.toToposHom
                (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G)))) ≫
        (PreservesLimitPair.iso f.toToposHom.inverseImage
              (moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F)
              (moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G)).inv ≫
          f.toToposHom.inverseImage.map b.1 ≫
            f.toToposHom.adj.counit.app
              (moduleSheaf (inverseImageRingSheaf f.toToposHom
                  (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
                ((SheafOfModules.restrictScalars f.fSharpInverseImage).obj N)) :=
  eq_prodMap_inv_comp
    ((moduleSheafFunctor
        (commRingSheaf X.J (inverseImageStructureCommRing f)
          (isSheaf_inverseImageStructureCommRing f))).map
      ((pullbackExtendAdj f).unit.app
        ((inverseImageModules f.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F)))
    ((moduleSheafFunctor
        (commRingSheaf X.J (inverseImageStructureCommRing f)
          (isSheaf_inverseImageStructureCommRing f))).map
      ((pullbackExtendAdj f).unit.app
        ((inverseImageModules f.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G)))
    _ _
    ((pullbackTensorStep3_apply_coe f F G N b).symm.trans
      (pullbackTensorStep3_apply_coe_eq_prodMap_unit_comp f F G N b))

end Value

end Stacks.SheafOfModules

end
