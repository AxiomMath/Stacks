module

public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposModulesPullbackToposGeneral
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraUnitEssentiallySmall
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorBilinEquivPairingApp

/-!
# The direct image along a morphism of ringed sites, on sections

For a morphism of ringed sites `f` presented by `u`, the direct image of sheaves of sets is
restriction along `u`, so it can be computed on local sections. This file records the sections of
the direct image of a product and of a bilinear pairing, which is what a computation of Stacks
03EL for such a morphism needs.

## Main results

* `AlgebraicGeometry.RingedSite.HomGeneral.sectionsFunctor_map_preservesLimitPair_inv_prodObjMk`:
  the inverse product comparison of the direct image, on a pair of sections over `u(V)`.
* `AlgebraicGeometry.RingedSite.HomGeneral.pairingApp_prodMap_comp_pushforward_map` and
  `pairingApp_prodMap_comp_pushforward_tensorSectionPairing`: a pairing `(a × b) ≫ f_*q`, and in
  particular `(η₁ × η₂) ≫ f_*(universal pairing)`, on local sections.
* That the comparison of the two pushforwards of modules is the identity on sections is not here:
  it is
  `AlgebraicGeometry.RingedSite.HomGeneral.pushforwardModulesToposIsoGeneral_hom_app_val_app`
  (`StacksFrontier/CategoryTheory/Sites/Modules/RingedSiteHomGeneralPushforwardUnderlying.lean`), at
  independent universes.

## References

* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.RingedToposModules
open scoped TensorProduct

universe uX vX uY vY w

namespace AlgebraicGeometry.RingedSite

open Stacks.SheafOfModules

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}} (f : HomGeneral X Y)

/-- The sections over `V` of the direct image of a morphism of sheaves of sets along a morphism of
ringed sites are its sections over `u(V)`. -/
theorem HomGeneral.sectionsFunctor_map_pushforward_map_apply {A B : Sheaf X.J (Type w)}
    (m : A ⟶ B) (V : Y.Cᵒᵖ) (a : (Sheaf.sectionsFunctor Y.J V).obj (f.toposHom.pushforward.obj A)) :
    (Sheaf.sectionsFunctor Y.J V).map (f.toposHom.pushforward.map m) a =
      (Sheaf.sectionsFunctor X.J (f.u.op.obj V)).map m a :=
  rfl

/-- The inverse of the product comparison of the direct image along a morphism of ringed sites,
on sections over `V`: a pair of sections over `u(V)` read in the product of the direct images is
carried to the same pair read in the product. -/
theorem HomGeneral.sectionsFunctor_map_preservesLimitPair_inv_prodObjMk
    (A B : Sheaf X.J (Type w)) (V : Y.Cᵒᵖ)
    (a : (Sheaf.sectionsFunctor X.J (f.u.op.obj V)).obj A)
    (b : (Sheaf.sectionsFunctor X.J (f.u.op.obj V)).obj B) :
    (Sheaf.sectionsFunctor Y.J V).map (PreservesLimitPair.iso f.toposHom.pushforward A B).inv
        (Functor.prodObjMk (P := Sheaf.sectionsFunctor Y.J V)
          (A := f.toposHom.pushforward.obj A) (B := f.toposHom.pushforward.obj B) a b) =
      Functor.prodObjMk (P := Sheaf.sectionsFunctor X.J (f.u.op.obj V)) a b := by
  apply ((Sheaf.sectionsFunctor Y.J V).mapIso
    (PreservesLimitPair.iso f.toposHom.pushforward A B)).toEquiv.injective
  show ((Sheaf.sectionsFunctor Y.J V).map (PreservesLimitPair.iso f.toposHom.pushforward A B).hom)
      (((Sheaf.sectionsFunctor Y.J V).map (PreservesLimitPair.iso f.toposHom.pushforward A B).inv)
        _) =
      ((Sheaf.sectionsFunctor Y.J V).map (PreservesLimitPair.iso f.toposHom.pushforward A B).hom)
      (Functor.prodObjMk (P := Sheaf.sectionsFunctor X.J (f.u.op.obj V)) (A := A) (B := B) a b)
  rw [← Functor.map_comp_apply, Iso.inv_hom_id, Functor.map_id_apply]
  refine (Functor.prodObjMk_ext ?_ ?_).symm <;>
    erw [← Functor.map_comp_apply, PreservesLimitPair.iso_hom]
  · erw [prodComparison_fst]
    exact (Functor.map_fst_prodObjMk (P := Sheaf.sectionsFunctor X.J (f.u.op.obj V)) a b).trans
      (Functor.map_fst_prodObjMk (P := Sheaf.sectionsFunctor Y.J V)
        (A := f.toposHom.pushforward.obj A) (B := f.toposHom.pushforward.obj B) a b).symm
  · erw [prodComparison_snd]
    exact (Functor.map_snd_prodObjMk (P := Sheaf.sectionsFunctor X.J (f.u.op.obj V)) a b).trans
      (Functor.map_snd_prodObjMk (P := Sheaf.sectionsFunctor Y.J V)
        (A := f.toposHom.pushforward.obj A) (B := f.toposHom.pushforward.obj B) a b).symm

variable [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget CommRingCat.{w})] [Y.J.HasSheafCompose (forget CommRingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})] [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]

omit [X.J.HasSheafCompose (forget CommRingCat)] [Y.J.HasSheafCompose (forget CommRingCat)] in
/-- **A pairing on the source carried to the target by the direct image, on sections.** For a
morphism of ringed sites, a pairing of the form `(a × b) ≫ f_*q` takes local sections `x`, `y`
over `V` to the value of `q` over `u(V)` on the images of `x` and `y`: the direct image is
restriction along `u`. -/
theorem HomGeneral.pairingApp_prodMap_comp_pushforward_map
    {P Q : SheafOfModules.{w} (Tensor.ringSheaf (toRingedTopos Y).O)}
    {A B N : SheafOfModules.{w} (Tensor.ringSheaf (toRingedTopos X).O)}
    (a : Sheaf.moduleSheaf _ P ⟶
      f.toRingedToposHom.toRingedToposModulesHom.toToposHom.pushforward.obj (Sheaf.moduleSheaf _ A))
    (b : Sheaf.moduleSheaf _ Q ⟶
      f.toRingedToposHom.toRingedToposModulesHom.toToposHom.pushforward.obj (Sheaf.moduleSheaf _ B))
    (q : Sheaf.moduleSheaf _ A ⨯ Sheaf.moduleSheaf _ B ⟶ Sheaf.moduleSheaf _ N) (V : Y.Cᵒᵖ)
    (x : (Sheaf.sectionsFunctor Y.J V).obj (Sheaf.moduleSheaf _ P))
    (y : (Sheaf.sectionsFunctor Y.J V).obj (Sheaf.moduleSheaf _ Q)) :
    pairingApp (Tensor.ringSheaf (toRingedTopos Y).O)
        (N := (pushforwardModules f.toRingedToposHom.toRingedToposModulesHom).obj N)
        (prod.map a b ≫
          (PreservesLimitPair.iso
            f.toRingedToposHom.toRingedToposModulesHom.toToposHom.pushforward _ _).inv ≫
          f.toRingedToposHom.toRingedToposModulesHom.toToposHom.pushforward.map q) V x y =
      pairingApp (Tensor.ringSheaf (toRingedTopos X).O) q (f.u.op.obj V)
        ((Sheaf.sectionsFunctor Y.J V).map a x) ((Sheaf.sectionsFunctor Y.J V).map b y) := by
  refine (pairingApp_eq_map_prodObjMk_of_eq_prodMap_comp (Tensor.ringSheaf (toRingedTopos Y).O)
    a b _ rfl V x y).trans ?_
  refine (Functor.map_comp_apply (Sheaf.sectionsFunctor Y.J V) _ _ _).trans ?_
  refine (congrArg ((Sheaf.sectionsFunctor Y.J V).map (f.toposHom.pushforward.map q))
    (f.sectionsFunctor_map_preservesLimitPair_inv_prodObjMk _ _ V _ _)).trans ?_
  rfl

omit [X.J.HasSheafCompose (forget CommRingCat)] [Y.J.HasSheafCompose (forget CommRingCat)] in
/-- **The pairing `(s, t) ↦ η(s) ⊗ η(t)` of Stacks 03EL for a morphism of ringed sites, on
sections.** For two morphisms `η₁ : P ⟶ f_*A` and `η₂ : Q ⟶ f_*B` of sheaves of modules, the
pairing `(η₁ × η₂) ≫ f_*(universal pairing of A and B)` takes local sections `x`, `y` over `V` to
the sheafification-unit image of `η₁(x) ⊗ η₂(y)` over `u(V)`. -/
theorem HomGeneral.pairingApp_prodMap_comp_pushforward_tensorSectionPairing
    [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    {P Q : SheafOfModules.{w} (Tensor.ringSheaf (toRingedTopos Y).O)}
    {A B : SheafOfModules.{w} (Tensor.ringSheaf (toRingedTopos X).O)}
    (η₁ : P ⟶ (pushforwardModules f.toRingedToposHom.toRingedToposModulesHom).obj A)
    (η₂ : Q ⟶ (pushforwardModules f.toRingedToposHom.toRingedToposModulesHom).obj B)
    (V : Y.Cᵒᵖ)
    (x : P.val.obj V) (y : Q.val.obj V) :
    pairingApp (Tensor.ringSheaf (toRingedTopos Y).O)
        (N := (pushforwardModules f.toRingedToposHom.toRingedToposModulesHom).obj
          (((Tensor.sheafTensor (toRingedTopos X).O).obj A).obj B))
        (prod.map ((Sheaf.moduleSheafFunctor (Tensor.ringSheaf (toRingedTopos Y).O)).map η₁)
            ((Sheaf.moduleSheafFunctor (Tensor.ringSheaf (toRingedTopos Y).O)).map η₂) ≫
          (PreservesLimitPair.iso f.toRingedToposHom.toRingedToposModulesHom.toToposHom.pushforward
            (Sheaf.moduleSheaf (Tensor.ringSheaf (toRingedTopos X).O) A)
            (Sheaf.moduleSheaf (Tensor.ringSheaf (toRingedTopos X).O) B)).inv ≫
          f.toRingedToposHom.toRingedToposModulesHom.toToposHom.pushforward.map
            (tensorSectionPairing A B)) V x y =
      _root_.PresheafOfModules.Hom.app ((PresheafOfModules.sheafificationAdjunction
          (R := Tensor.ringSheaf (toRingedTopos X).O)
          (𝟙 (Tensor.ringSheaf (toRingedTopos X).O).obj)).unit.app
        (PresheafOfModules.tensorObj (O := (toRingedTopos X).O.obj) A.val B.val))
        (f.u.op.obj V)
        (η₁.val.app V x ⊗ₜ[((toRingedTopos X).O.obj ⋙ forget₂ CommRingCat RingCat).obj
          (f.u.op.obj V)] η₂.val.app V y) :=
  (f.pairingApp_prodMap_comp_pushforward_map _ _ _ V x y).trans
    (pairingApp_tensorSectionPairing _ _ _ _ _)

end AlgebraicGeometry.RingedSite

end
