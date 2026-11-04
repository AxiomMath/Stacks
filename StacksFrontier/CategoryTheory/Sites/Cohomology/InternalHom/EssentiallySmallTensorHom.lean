module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.BilinearInternalHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PowerPresentationSequences
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EssentiallySmallInternalHom

/-!
# The tensor–Hom correspondence on an essentially small ringed site

Let `X` be a ringed site whose underlying category is essentially `m`-small, and let `H`, `F`,
`G` be sheaves of modules with sections in `m`.  Then

`Hom(H ⊗ F, G) = Hom(H, Hom(F, G))`,

where `H ⊗ F` is the tensor product of sheaves of modules (the sheafification of the
objectwise tensor product) and `Hom(F, G)` is the internal Hom of Stacks 03EM read in the
module universe `m`, `AlgebraicGeometry.RingedSite.internalHomSheafSmall`.  This is the sheaf
clause of Stacks 03EO at a module universe not tied to the universes of the site.

## Main definitions

* `AlgebraicGeometry.RingedSite.tensorHomEquivInternalHomSheafSmall`: the correspondence.

## Implementation notes

The correspondence is assembled from four bijections, none of which is new:

* a morphism out of the sheafified tensor product is a morphism out of the objectwise tensor
  product (`PresheafOfModules.sheafificationHomEquiv`), that is a bilinear map of sections
  (`PresheafOfModules.ofBilinear`, `PresheafOfModules.toBilinear`);
* a bilinear map `H × F → G` is a bilinear map `ULift H × F → G`;
* such a bilinear map is a morphism `ULift H ⟶ Hom(F, G)` into the internal Hom presheaf
  (`Stacks.PresheafOfModules.bilinearEquivHomInternalHom`), whose sections live in the larger
  universe;
* and, by `AlgebraicGeometry.RingedSite.internalHomSheafSmallIso` and the full faithfulness of
  the universe lift, that is a morphism `H ⟶ internalHomSheafSmall X F G`.

## References

* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 03EO](https://stacks.math.columbia.edu/tag/03EO)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe m u v w

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, v, w}) [EssentiallySmall.{m} X.C]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasWeakSheafify X.J AddCommGrpCat.{m}]

variable {X} in
/-- Morphisms out of the objectwise tensor product of two presheaves of modules are the bilinear
maps of sections. -/
def tensorObjHomEquivBilinear {H F G : PresheafOfModules.{m} (Oforget X.O.obj)} :
    (PresheafOfModules.tensorObj (O := X.O.obj) H F ⟶ G) ≃ Stacks.BilinearMap H F G where
  toFun := PresheafOfModules.toBilinear
  invFun := PresheafOfModules.ofBilinear
  left_inv _φ := PresheafOfModules.tensorObj_hom_ext fun U x y =>
    PresheafOfModules.ofBilinear_tmul _ U x y
  right_inv β := Stacks.BilinearMap.ext fun U x y => PresheafOfModules.ofBilinear_tmul β U x y

/-- **Stacks 03EO, sheaf case, on an essentially small ringed site.**  For sheaves of modules
`H`, `F`, `G` with sections in `m` on a ringed site which is essentially `m`-small, morphisms
`H ⊗ F ⟶ G` out of the sheaf tensor product correspond to morphisms `H ⟶ Hom(F, G)` into the
internal Hom of Stacks 03EM, read in the universe `m`. -/
def tensorHomEquivInternalHomSheafSmall
    (H F G : SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, m, m} X.O).obj H).obj F ⟶ G) ≃
      (H ⟶ internalHomSheafSmall X F G) :=
  (PresheafOfModules.sheafificationHomEquiv
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).trans <|
    tensorObjHomEquivBilinear.trans <|
    Stacks.BilinearMap.uliftEquiv.trans <|
    Stacks.PresheafOfModules.bilinearEquivHomInternalHom.trans <|
    (show ((Stacks.SheafOfModules.presheafULift.{max u v}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj).obj H.val ⟶
          internalHom X.O.obj (valOf X F) (valOf X G)) ≃
        ((Stacks.SheafOfModules.moduleULift.{max u v}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj H ⟶ internalHomSheaf X F G) from
      { toFun := fun f => ⟨f⟩
        invFun := fun f => f.val
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }).trans <|
    ((Iso.refl _).homCongr (internalHomSheafSmallIso X F G).symm).trans
      (Stacks.SheafOfModules.moduleULiftFullyFaithful.{max u v}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).homEquiv.symm

/-- **The correspondence is currying.**  After raising the universe of `H` and identifying
`internalHomSheafSmall X F G` with the internal Hom of Stacks 03EM, the morphism attached to
`b : H ⊗ F ⟶ G` sends a section `x` of `H` over `U` to the morphism `F|_U ⟶ G|_U` which over
`V → U` is `y ↦ b(x|_V ⊗ y)`. -/
theorem tensorHomEquivInternalHomSheafSmall_apply
    {H F G : SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (b : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, m, m} X.O).obj H).obj F ⟶ G) :
    ((Stacks.SheafOfModules.moduleULift.{max u v}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map
        (tensorHomEquivInternalHomSheafSmall X H F G b) ≫
        (internalHomSheafSmallIso X F G).hom).val =
      Stacks.PresheafOfModules.curryBilinear (C := X.C) (O := X.O.obj)
        (K := (Stacks.SheafOfModules.presheafULift.{max u v}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj).obj H.val)
        (G := valOf X F) (H := valOf X G) (Stacks.BilinearMap.ulift
        (PresheafOfModules.toBilinear (show PresheafOfModules.tensorObj (O := X.O.obj) H.val F.val ⟶
          G.val from PresheafOfModules.sheafificationHomEquiv
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) b))) := by
  have key : ∀ g : (Stacks.SheafOfModules.moduleULift.{max u v}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj H ⟶ internalHomSheaf X F G,
      (Stacks.SheafOfModules.moduleULift.{max u v}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map
        ((Stacks.SheafOfModules.moduleULiftFullyFaithful.{max u v}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).preimage
            (𝟙 _ ≫ g ≫ (internalHomSheafSmallIso X F G).inv)) ≫
        (internalHomSheafSmallIso X F G).hom = g := fun g => by simp
  exact congrArg SheafOfModules.Hom.val (key ⟨_⟩)

end AlgebraicGeometry.RingedSite
