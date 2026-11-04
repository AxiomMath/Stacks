module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BilinearValueFormulas
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensor

/-!
# The pairing induced by a morphism out of a tensor product sheaf

The universal property of the tensor product sheaf over the structure sheaf `O_D` of the target,

`Hom_{O_D}(F ⊗ G, f_*N) = Bilin_{O_D}(F × G, f_*N)`,

traversed from morphisms to pairings, is `Stacks.SheafOfModules.pullbackTensorStep2`, step 2 of
the chain of bijections of Tag 03EL. This file evaluates it on an arbitrary morphism `g`: the
pairing it induces is `Stacks.SheafOfModules.pairingOfTensorHom` of the sheafification unit
followed by `g`, equivalently the universal bilinear pairing
`Stacks.SheafOfModules.tensorSectionPairing` of Tag 05NA followed by `g`.

## Main results

* `Stacks.SheafOfModules.bilinearEquivTensorSheafHom_symm_apply_coe`: the bilinear pairing
  recovered from a morphism out of the tensor product sheaf is the pairing of the sheafification
  unit followed by that morphism.
* `Stacks.SheafOfModules.bilinearEquivTensorSheafHom_symm_id_coe`: the pairing recovered from the
  identity is the pairing of the sheafification unit alone.
* `Stacks.SheafOfModules.pullbackTensorStep2_apply_coe` and
  `Stacks.SheafOfModules.pullbackTensorStep2_apply`: the pairing step 2 produces from `g` is the
  pairing of the sheafification unit followed by `g`, as a pairing and as an element of the
  subtype of bilinear pairings.
* `Stacks.SheafOfModules.pullbackTensorStep2_apply_coe_eq_tensorSectionPairing_comp`: the pairing
  step 2 produces from `g` is the universal bilinear pairing followed by `g`.
* `Stacks.SheafOfModules.unit_comp_pullbackTensorStep2_symm_apply_val`: the morphism out of
  `F ⊗_{O_D} G` determined by a pairing, restricted along the sheafification unit, is
  `Stacks.SheafOfModules.tensorHomOfPairing` of that pairing.

## Implementation notes

The sheaf of rings `O_D` has two spellings, `Stacks.SheafOfModules.Tensor.ringSheaf Y.O` and the
`Stacks.Sheaves.RingedToposModules.commRingSheaf` of a presheaf of commutative rings with a sheaf
condition, which are definitionally equal only at default transparency. The statements about
`Stacks.SheafOfModules.bilinearEquivTensorSheafHom` use the second spelling and those about
`Stacks.SheafOfModules.pullbackTensorStep2` the first.

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CategoryTheory.Sheaf
open AlgebraicGeometry.SheafOfModules Stacks.Sheaves.RingedToposModules
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.PresheafOfModules.ChangeOfRings

namespace Stacks.SheafOfModules

universe w v u

/-! ## The pairing induced by a morphism out of the tensor product sheaf -/

section TensorSheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {A : Cᵒᵖ ⥤ CommRingCat.{w}} {hA : Presheaf.IsSheaf J (ringPresheaf A)}
  {F G N : SheafOfModules.{w} (commRingSheaf J A hA)}

/-- The bilinear pairing recovered from a morphism `t` out of the tensor product sheaf `F ⊗_A G`
is the pairing of the restriction of `t` along the sheafification unit of `F.val ⊗ G.val`, as an
equality of pairings of the underlying sheaves of sets. -/
lemma bilinearEquivTensorSheafHom_symm_apply_coe
    (t : ((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨A, Presheaf.isSheaf_of_isSheaf_comp _ A (forget₂ CommRingCat RingCat) hA⟩).obj F).obj G ⟶
        N) :
    ((bilinearEquivTensorSheafHom (F := F) (G := G) (N := N)).symm t).1 =
      pairingOfTensorHom (hO := hA)
        ((PresheafOfModules.sheafificationAdjunction (R := commRingSheaf J A hA) (𝟙 _)).unit.app
          (F.val ⊗ G.val) ≫ t.val) :=
  congrArg (fun p ↦ pairingOfTensorHom (hO := hA) p)
    (tensorSheafHomEquivPresheafTensorHom_apply t)

/-- The bilinear pairing recovered from the identity of the tensor product sheaf `F ⊗_A G` is
the pairing of the sheafification unit of `F.val ⊗ G.val`. -/
lemma bilinearEquivTensorSheafHom_symm_id_coe :
    ((bilinearEquivTensorSheafHom (F := F) (G := G)
        (N := ((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨A, Presheaf.isSheaf_of_isSheaf_comp _ A (forget₂ CommRingCat RingCat) hA⟩).obj F).obj
            G)).symm (𝟙 _)).1 =
      pairingOfTensorHom (hO := hA) (A := F) (B := G)
          (N := ((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨A, Presheaf.isSheaf_of_isSheaf_comp _ A (forget₂ CommRingCat RingCat) hA⟩).obj F).obj G)
        ((PresheafOfModules.sheafificationAdjunction (R := commRingSheaf J A hA) (𝟙 _)).unit.app
          (F.val ⊗ G.val)) :=
  (bilinearEquivTensorSheafHom_symm_apply_coe _).trans (congrArg _ (Category.comp_id _))

end TensorSheaf

/-! ## Step 2 of the chain of Tag 03EL -/

section Step2

universe w' v' u'

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  (f : RingedToposHom X Y)
  (F G : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
  (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The bilinear pairing of `F` and `G` with values in `f_*N` which step 2 of the chain of
Tag 03EL produces from a morphism `g : F ⊗_{O_D} G ⟶ f_*N` is the pairing of the sheafification
unit of the tensor product sheaf followed by `g`. -/
theorem pullbackTensorStep2_apply_coe
    (g : ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O))).obj (F, G) ⟶
      (pushforwardModules f).obj N) :
    (pullbackTensorStep2 f F G N g).1 =
      pairingOfTensorHom (hO := (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property)
        ((PresheafOfModules.sheafificationAdjunction
              (R := Stacks.SheafOfModules.Tensor.ringSheaf Y.O) (𝟙 _)).unit.app
            (F.val ⊗ G.val) ≫ g.val) :=
  bilinearEquivTensorSheafHom_symm_apply_coe
    (hA := (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property) g

omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- Step 2 of the chain of Tag 03EL sends a morphism `g : F ⊗_{O_D} G ⟶ f_*N` to the bilinear
pairing of the sheafification unit of the tensor product sheaf followed by `g`, as an element of
the subtype of bilinear pairings. -/
theorem pullbackTensorStep2_apply
    (g : ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O))).obj (F, G) ⟶
      (pushforwardModules f).obj N) :
    pullbackTensorStep2 f F G N g =
      ⟨pairingOfTensorHom (hO := (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property)
          ((PresheafOfModules.sheafificationAdjunction
                (R := Stacks.SheafOfModules.Tensor.ringSheaf Y.O) (𝟙 _)).unit.app
              (F.val ⊗ G.val) ≫ g.val),
        isBilinearPairing_pairingOfTensorHom
          (hO := (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property) _⟩ :=
  Subtype.ext (pullbackTensorStep2_apply_coe f F G N g)

omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The bilinear pairing which step 2 of the chain of Tag 03EL produces from
`g : F ⊗_{O_D} G ⟶ f_*N` is the universal pairing `Stacks.SheafOfModules.tensorSectionPairing`
of Tag 05NA, which pairs two local sections to the sheafification-unit image of their tensor,
followed by `g` on underlying sheaves of sets. -/
theorem pullbackTensorStep2_apply_coe_eq_tensorSectionPairing_comp
    (g : ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O))).obj (F, G) ⟶
      (pushforwardModules f).obj N) :
    (pullbackTensorStep2 f F G N g).1 =
      tensorSectionPairing F G ≫
        (moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map g :=
  ((congrArg (fun t ↦ ((bilinearEquivTensorSheafHom
              (hA := (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property) (F := F) (G := G)
              (N := (pushforwardModules f).obj N)).symm t).1)
          (Category.id_comp g).symm).trans
        (congrArg Subtype.val (bilinearEquivTensorSheafHom_symm_naturality
          (hA := (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property) (F := F) (G := G)
          (𝟙 _) g))).trans
    (congrArg (fun p ↦ p ≫ (moduleSheafFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map g)
      (bilinearEquivTensorSheafHom_symm_id_coe
        (hA := (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property) (F := F) (G := G)))

omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The morphism `F ⊗_{O_D} G ⟶ f_*N` which step 2 of the chain of Tag 03EL determines from a
bilinear pairing `q`, restricted along the sheafification unit of the tensor product sheaf, is
`Stacks.SheafOfModules.tensorHomOfPairing` of `q`: the morphism out of the objectwise tensor
product which takes a pure tensor to the value of `q`. -/
theorem unit_comp_pullbackTensorStep2_symm_apply_val
    (q : { q : moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F ⨯
          moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G ⟶
          moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
            ((pushforwardModules f).obj N) //
        IsBilinearPairing (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) q }) :
    (PresheafOfModules.sheafificationAdjunction
            (R := Stacks.SheafOfModules.Tensor.ringSheaf Y.O) (𝟙 _)).unit.app (F.val ⊗ G.val) ≫
        ((pullbackTensorStep2 f F G N).symm q).val =
      tensorHomOfPairing (hO := (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property) q.2 :=
  unit_comp_bilinearEquivTensorSheafHom_val
    (hA := (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property) q

end Step2

end Stacks.SheafOfModules

end
