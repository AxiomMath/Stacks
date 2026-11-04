module

public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.SheafTensorHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InternalHomVariance
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InternalHomRestriction
public import StacksFrontier.CategoryTheory.Sites.Modules.ExtensionByZeroExactness
public import StacksFrontier.CategoryTheory.Sites.Modules.LocalizationRingedSites.DirectImage
public import StacksFrontier.CategoryTheory.Sites.Modules.Flat
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforward
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.InternalHomFirstVariable
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BifunctorReductionMachinery
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.TensorSymmetry
public import StacksFrontier.CategoryTheory.Adjunction.ConjugateNaturality
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import StacksCore.Tactic.StacksAttribute

/-!
# Extension by zero and tensor products on a ringed site

Let `(C, O)` be a ringed site and `U` an object of `C`. Extension by zero from the localized
site `C/U`, the left adjoint `E` of restriction, commutes with tensoring by a sheaf of
`O`-modules `F`: for a sheaf of `O|_U`-modules `G`,

`E(G) ⊗_O F = E(G ⊗_{O|_U} F|_U)`,

naturally in `G` and in `F`. This is Stacks 0E8I.

## Main results

* `Stacks.SheafOfModules.ExtensionByZero.extensionByZeroTensorIso` is the natural isomorphism
  for a fixed `F`, stated as an isomorphism of functors in the module on the slice site.
* `Stacks.SheafOfModules.ExtensionByZero.extensionTensorBifunctorIso` is the bifunctorial form:
  the same isomorphism read as an isomorphism of the two bifunctors
  `F ↦ (G ↦ E(G) ⊗_O F)` and `F ↦ (G ↦ E(G ⊗_{O|_U} F|_U))`, hence natural in `F` as well.
* `Stacks.SheafOfModules.ExtensionByZero.conjugateEquiv_sheafTensor_map` is what makes the
  second variable work: the tensor--internal-Hom adjunction of Stacks 03EO is *parametrised* in
  the tensor factor, in that the conjugate of tensoring by `φ : F ⟶ F'` is precomposition by
  `φ` on internal Hom.

## Implementation notes

Both sides are left adjoints: of internal Hom out of `F` composed with restriction, and of
restriction composed with internal Hom out of `F|_U`. Those two right adjoints agree by Stacks
0E8H, so the isomorphism is uniqueness of left adjoints. The tensor--internal-Hom adjunction
itself is Stacks 03EO, whose correspondence `sheafTensorHomEquivPlain` tensors on the *right*;
the canonical symmetry `Stacks.SheafOfModules.Tensor.sheafTensorBraiding` of `⊗_O` turns it into
the left tensor functor of Stacks 05NB.

**No local symmetry is introduced here.** A hand-assembled `(sheafTensor O).obj F ≅ (sheafTensor O).flip.obj F` built
from `BraidedCategory.braiding` on presheaves of modules and whiskered through
`SheafOfModules.forget` and `PresheafOfModules.sheafification` would be the construction of
`Stacks.SheafOfModules.Tensor.sheafTensorBraiding` itself, inlined: same type at the component,
same recipe, no extra content. The component `(sheafTensorBraiding O).app F` is what this file
uses, and it is the library's one braiding of `⊗_O`.

Both tensor factors use the ordinary canonical `Tensor.ringSheaf` index. Right tensoring is
read directly from the native presheaf and sheaf tensor bifunctors through `.flip.obj`. The
symmetry is taken at its component `(sheafTensorBraiding O).app F`, so the interchange of the
two factors is the repo's one braiding of `⊗_O` rather than a second copy of it, and the
tensor--internal-Hom correspondence uses its existing sectionwise description without a second
right-tensor construction or a separate adjunction spelling.

The bifunctorial form is uniqueness of left adjoints again, now for two *families* of
adjunctions; `Stacks.CategoryTheory.leftAdjointUniq_naturality_of_eq` reduces its naturality
square to the equality of two conjugates, and Mathlib's `conjugateEquiv_whiskerLeft` and
`conjugateEquiv_whiskerRight` reduce that to three facts: that Stacks 03EO is parametrised in
the tensor factor (`conjugateEquiv_sheafTensor_map`), that Stacks 0E8H is natural in the source
module (`internalHomRestrictionNatIso_naturality`), and the behaviour of a conjugate under
`Adjunction.ofNatIsoRight`.

Left tensoring uses the canonical bifunctor `Stacks.SheafOfModules.Tensor.sheafTensor`
throughout the bifunctorial statement. The right adjoint of extension by zero occurs as
`SheafOfModules.pushforward` and as `SheafOfModules.overFunctor`;
`extensionByZeroAdjunction` fixes the second, which is the spelling Stacks 0E8H uses, so that
the two adjunctions compared by uniqueness of left adjoints have literally the same right
adjoint.

## References

* [Stacks Project, Tag 0E8I](https://stacks.math.columbia.edu/tag/0E8I)
* [Stacks Project, Tag 0E8H](https://stacks.math.columbia.edu/tag/0E8H), internal Hom and
  restriction.
* [Stacks Project, Tag 03EO](https://stacks.math.columbia.edu/tag/03EO), the
  tensor--internal-Hom adjunction.
* [Stacks Project, Tag 05NB](https://stacks.math.columbia.edu/tag/05NB), the tensor product of
  sheaves of modules.
-/

@[expose] public section

open CategoryTheory MonoidalCategory Opposite AlgebraicGeometry
open Stacks.SheafOfModules.InternalHom (sheafTensorHomEquivPlain sheafTensorHomEquivPlain_apply
  internalHomSecondFunctor internalHomOverIso sheafInternalHomMapLeft)
open Stacks.PresheafOfModules.InternalHom (presheafTensorHomEquiv_section_apply)
open Stacks.SheafOfModules.Tensor (sheafTensor sheafTensorBraiding)
open Stacks.CategoryTheory (conjugateEquiv_eq_of_homEquiv conjugateEquiv_ofNatIsoRight
  leftAdjointUniq_naturality_of_eq)

namespace Stacks.SheafOfModules.ExtensionByZero

attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf

universe u

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
  (O : Sheaf J CommRingCat.{u})

/-- The tensor--internal-Hom correspondence sends `b` to the morphism locally given by
`x ↦ (y ↦ b (x ⊗ y))`. -/
theorem tensorHomEquiv_apply (F G' H : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (J := J) O))
    (b : (((sheafTensor.{u, u, u, u, u} O).flip.obj F)).obj G' ⟶ H) (U : C)
    (x : G'.val.obj (op U)) (y : F.val.obj (op U)) :
    (((sheafTensorHomEquivPlain J O G' F H b).val.app (op U) x).app
      (op (Over.mk (𝟙 U)))).hom y =
      b.val.app (op U)
        (((_root_.PresheafOfModules.sheafificationAdjunction
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (J := J) O).obj)).unit.app
              ((((_root_.PresheafOfModules.tensorBifunctor.{u, u, u, u, u} O.obj).flip.obj F.val)).obj G'.val)).app (op U)
          (x ⊗ₜ[O.obj.obj (op U)] y)) :=
  sheafTensorHomEquivPlain_apply J O G' F H b U x y

/-- **Stacks 03EO**, read as an adjunction: tensoring by `F` is left adjoint to internal Hom
out of `F`. -/
noncomputable def sheafTensorHomAdjunction (F : _root_.SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf (J := J) O)) :
    ((sheafTensor.{u, u, u, u, u} O).obj F) ⊣ internalHomSecondFunctor J O F := by
  let shAdj := _root_.PresheafOfModules.sheafificationAdjunction
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (J := J) O).obj)
  let sh := _root_.PresheafOfModules.sheafification (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (J := J) O).obj)
  let tensor := ((_root_.PresheafOfModules.tensorBifunctor.{u, u, u, u, u} O.obj).flip.obj F.val)
  let G := internalHomSecondFunctor J O F
  let adj : Adjunction.CoreHomEquiv (((sheafTensor.{u, u, u, u, u} O).flip.obj F)) G :=
    { homEquiv := fun G' H => sheafTensorHomEquivPlain J O G' F H
      homEquiv_naturality_left_symm := by
        intro X' X Y f g
        let e' := sheafTensorHomEquivPlain J O X' F Y
        let e := sheafTensorHomEquivPlain J O X F Y
        apply (shAdj.homEquiv (tensor.obj X'.val) Y).injective
        change shAdj.homEquiv (tensor.obj X'.val) Y (e'.symm (f ≫ g)) =
          shAdj.homEquiv (tensor.obj X'.val) Y
            (sh.map (tensor.map f.val) ≫ e.symm g)
        refine Eq.trans ?_
          (shAdj.homEquiv_naturality_left (tensor.map f.val) (e.symm g)).symm
        apply _root_.PresheafOfModules.hom_ext
        intro U
        apply ModuleCat.MonoidalCategory.tensor_ext
        intro x y
        have hleft := tensorHomEquiv_apply J O F X' Y (e'.symm (f ≫ g)) U.unop x y
        have hright := tensorHomEquiv_apply J O F X Y (e.symm g) U.unop (f.val.app U x) y
        have hleft := (congrArg
          (fun morphism : X' ⟶ Stacks.SheafOfModules.InternalHom.siteSheafInternalHom J O F Y =>
            ((morphism.val.app U x).app (op (Over.mk (𝟙 U.unop)))).hom y)
          (e'.apply_symm_apply (f ≫ g))).symm.trans hleft
        have hright := (congrArg
          (fun morphism : X ⟶ Stacks.SheafOfModules.InternalHom.siteSheafInternalHom J O F Y =>
            ((morphism.val.app U (f.val.app U x)).app
              (op (Over.mk (𝟙 U.unop)))).hom y)
          (e.apply_symm_apply g)).symm.trans hright
        have hcomp :
            ((((f ≫ g).val.app U x).app (op (Over.mk (𝟙 (unop U))))).hom y) =
              ((((g.val.app U) (f.val.app U x)).app
                (op (Over.mk (𝟙 (unop U))))).hom y) := rfl
        have hright' := by
          have h := shAdj.homEquiv_unit (tensor.obj X.val) Y (e.symm g)
          exact congrArg
            (fun k => (k.app U).hom ((tensor.map f.val).app U
              (x ⊗ₜ[O.obj.obj U] y))) h |>.symm
        have hscalar :
            (e.symm g).val.app U
                (((shAdj.unit.app (tensor.obj X.val)).app U).hom
                  (((tensor.map f.val).app U).hom (x ⊗ₜ[O.obj.obj U] y))) =
              ((ModuleCat.restrictScalars
                (RingCat.Hom.hom (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J) O).obj.obj U)))).map
                  ((e.symm g).val.app U)).hom
                (((shAdj.unit.app (tensor.obj X.val)).app U).hom
                  (((tensor.map f.val).app U).hom (x ⊗ₜ[O.obj.obj U] y))) := rfl
        exact hleft.symm.trans (hcomp.trans (hright.trans (hscalar.trans hright'))) }
  exact (Adjunction.mkOfHomEquiv adj).ofNatIsoLeft ((sheafTensorBraiding.{u, u, u} O).app F).symm

/-- The tensor--internal-Hom correspondence read on sections over an arbitrary object `V ⟶ U` of the
slice category: `b` goes to `x ↦ (y ↦ b (x|_V ⊗ y))`. This is `tensorHomEquiv_apply` with the
object of the slice left free, which is what an equality of sections of an internal Hom sheaf
needs. -/
theorem tensorHomEquiv_section_apply
    (F G' H : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (J := J) O))
    (b : (((sheafTensor.{u, u, u, u, u} O).flip.obj F)).obj G' ⟶ H) (U : C)
    (x : G'.val.obj (op U)) (V : (Over U)ᵒᵖ)
    (y : F.val.obj (op V.unop.left)) :
    (((sheafTensorHomEquivPlain J O G' F H b).val.app (op U) x).app V).hom y =
      b.val.app (op V.unop.left)
        ((((_root_.PresheafOfModules.sheafificationAdjunction.{u} (R := Stacks.SheafOfModules.Tensor.ringSheaf O) (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).unit).app ((((_root_.PresheafOfModules.tensorBifunctor.{u, u, u, u, u} O.obj).flip.obj F.val)).obj G'.val)).app
            (op V.unop.left)
          (G'.val.map V.unop.hom.op x ⊗ₜ[O.obj.obj (op V.unop.left)] y)) :=
  presheafTensorHomEquiv_section_apply O.obj G'.val F.val H.val _ U x V y

/-- Sheafification of a morphism of presheaves of modules, read on a section of the unit. -/
private theorem sheafification_map_unit_app_apply
    {P Q : PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (J := J) O).obj}
    (f : P ⟶ Q) (U : Cᵒᵖ) (a : P.obj U) :
    ((_root_.PresheafOfModules.sheafification.{u}
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (J := J) O).obj)).map f).val.app U
        (((_root_.PresheafOfModules.sheafificationAdjunction
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (J := J) O).obj)).unit.app P).app U a) =
      ((_root_.PresheafOfModules.sheafificationAdjunction
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (J := J) O).obj)).unit.app Q).app U
          (f.app U a) := by
  have := ‹J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})›
  exact (congrArg (fun k => (ConcreteCategory.hom (k.app U)) a)
    ((_root_.PresheafOfModules.sheafificationAdjunction
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (J := J) O).obj)).unit.naturality f)).symm

/-- The canonical symmetry `Stacks.SheafOfModules.Tensor.sheafTensorBraiding` of `⊗_O` read on a
pure tensor: it swaps the two factors. -/
theorem sheafTensorBraiding_inv_app_sheafifyUnit_tmul
    (F G : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (J := J) O)) (U : C)
    (x : G.val.obj (op U)) (y : F.val.obj (op U)) :
    (((sheafTensorBraiding.{u, u, u} O).app F).inv.app G).val.app (op U)
        ((((_root_.PresheafOfModules.sheafificationAdjunction.{u} (R := Stacks.SheafOfModules.Tensor.ringSheaf O) (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).unit).app ((((_root_.PresheafOfModules.tensorBifunctor.{u, u, u, u, u} O.obj).flip.obj F.val)).obj G.val)).app (op U)
          (x ⊗ₜ[O.obj.obj (op U)] y)) =
      (((_root_.PresheafOfModules.sheafificationAdjunction.{u} (R := Stacks.SheafOfModules.Tensor.ringSheaf O) (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).unit).app ((((_root_.PresheafOfModules.tensorBifunctor.{u, u, u, u, u} O.obj).obj F.val)).obj G.val)).app (op U)
        (y ⊗ₜ[O.obj.obj (op U)] x) := by
  exact sheafification_map_unit_app_apply J O
    (BraidedCategory.braiding F.val G.val).inv (op U) (x ⊗ₜ[O.obj.obj (op U)] y)

/-- Tensoring a pure tensor by `φ` in the left-hand factor. -/
theorem sheafTensor_map_app_sheafifyUnit_tmul
    {F F' : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (J := J) O)} (φ : F ⟶ F')
    (G : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (J := J) O)) (U : C)
    (y : F.val.obj (op U)) (x : G.val.obj (op U)) :
    (((sheafTensor.{u, u, u, u, u} O).map φ).app G).val.app (op U)
        ((((_root_.PresheafOfModules.sheafificationAdjunction.{u} (R := Stacks.SheafOfModules.Tensor.ringSheaf O) (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).unit).app ((((_root_.PresheafOfModules.tensorBifunctor.{u, u, u, u, u} O.obj).obj F.val)).obj G.val)).app (op U)
          (y ⊗ₜ[O.obj.obj (op U)] x)) =
      (((_root_.PresheafOfModules.sheafificationAdjunction.{u} (R := Stacks.SheafOfModules.Tensor.ringSheaf O) (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).unit).app ((((_root_.PresheafOfModules.tensorBifunctor.{u, u, u, u, u} O.obj).obj F'.val)).obj G.val)).app (op U)
        (φ.val.app (op U) y ⊗ₜ[O.obj.obj (op U)] x) := by
  exact sheafification_map_unit_app_apply J O (MonoidalCategory.whiskerRight φ.val G.val) (op U)
    (y ⊗ₜ[O.obj.obj (op U)] x)

/-- The hom-set bijection of `sheafTensorHomAdjunction` read on sections: it sends `f` to the
morphism `x ↦ (y ↦ f (y ⊗ x|_V))`. -/
theorem tensorHomAdjunction_homEquiv_section_apply
    (F G H : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (J := J) O))
    (f : (((sheafTensor.{u, u, u, u, u} O).obj F)).obj G ⟶ H) (U : C)
    (x : G.val.obj (op U)) (V : (Over U)ᵒᵖ)
    (y : F.val.obj (op V.unop.left)) :
    ((((sheafTensorHomAdjunction J O F).homEquiv G H f).val.app (op U) x).app V).hom y =
      f.val.app (op V.unop.left)
        ((((_root_.PresheafOfModules.sheafificationAdjunction.{u} (R := Stacks.SheafOfModules.Tensor.ringSheaf O) (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).unit).app ((((_root_.PresheafOfModules.tensorBifunctor.{u, u, u, u, u} O.obj).obj F.val)).obj G.val)).app
            (op V.unop.left)
          (y ⊗ₜ[O.obj.obj (op V.unop.left)]
            G.val.map V.unop.hom.op x)) := by
  have hadj : (sheafTensorHomAdjunction J O F).homEquiv G H f =
      sheafTensorHomEquivPlain J O G F H
        (((sheafTensorBraiding.{u, u, u} O).app F).inv.app G ≫ f) :=
    Adjunction.homEquiv_ofNatIsoLeft_apply _ _ f
  refine (congrArg
    (fun morphism : G ⟶ (internalHomSecondFunctor J O F).obj H =>
      ((morphism.val.app (op U) x).app V).hom y) hadj).trans ?_
  refine (tensorHomEquiv_section_apply J O F G H
    (((sheafTensorBraiding.{u, u, u} O).app F).inv.app G ≫ f) U x V y).trans ?_
  exact congrArg (f.val.app (op V.unop.left))
    (sheafTensorBraiding_inv_app_sheafifyUnit_tmul J O F G V.unop.left
      (G.val.map V.unop.hom.op x) y)

/-- Precomposition by `φ` in the first variable of internal Hom, as a natural transformation
between the internal-Hom functors in the second variable. -/
noncomputable def internalHomSecondFunctorMapLeft
    {F F' : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (J := J) O)} (φ : F ⟶ F') :
    internalHomSecondFunctor J O F' ⟶ internalHomSecondFunctor J O F where
  app _ := sheafInternalHomMapLeft J O φ
  naturality _ _ _ := rfl

/-- **The tensor--internal-Hom adjunction of Stacks 03EO is parametrised in the tensor factor:**
the conjugate of tensoring by `φ : F ⟶ F'` is precomposition by `φ` on internal Hom. -/
theorem conjugateEquiv_sheafTensor_map
    {F F' : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (J := J) O)} (φ : F ⟶ F') :
    conjugateEquiv (sheafTensorHomAdjunction J O F') (sheafTensorHomAdjunction J O F)
        ((sheafTensor.{u, u, u, u, u} O).map φ) =
      internalHomSecondFunctorMapLeft J O φ := by
  refine conjugateEquiv_eq_of_homEquiv _ _ _ _ ?_
  intro G H b
  apply _root_.SheafOfModules.hom_ext
  apply _root_.PresheafOfModules.hom_ext; intro U
  apply ModuleCat.hom_ext; apply LinearMap.ext; intro x
  apply _root_.PresheafOfModules.hom_ext; intro V
  apply ModuleCat.hom_ext; apply LinearMap.ext; intro y
  refine Eq.trans (tensorHomAdjunction_homEquiv_section_apply J O F G H _ U.unop x V y) ?_
  refine Eq.trans ?_ (tensorHomAdjunction_homEquiv_section_apply J O F' G H b U.unop x V
    (φ.val.app (op V.unop.left) y)).symm
  exact congrArg (b.val.app (op V.unop.left))
    (sheafTensor_map_app_sheafifyUnit_tmul J O φ G V.unop.left y (G.val.map V.unop.hom.op x))

variable (X : RingedSite.{u, u, u}) (U : X.C)

section Restriction

variable [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(X.J.over U).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify (X.J.over U) AddCommGrpCat.{u}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **Stacks 0E8H**, read functorially: internal Hom out of `F` commutes with restriction to
the localized site over `U`. -/
@[sga "4 IV 12.3" "(b)", sga "4 IV 12.5" "special case"]
noncomputable def internalHomRestrictionNatIso (F : _root_.SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    internalHomSecondFunctor X.J X.O F ⋙
        _root_.SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O) U ≅
      _root_.SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O) U ⋙
        internalHomSecondFunctor (X.J.over U) (X.O.over U) (F.over U) := by
  refine NatIso.ofComponents
    (fun H => (_root_.SheafOfModules.fullyFaithfulForget _).preimageIso
      (internalHomOverIso X U F H)) ?_
  intro H H' f
  rfl

/-- **Stacks 0E8I.** Extension by zero commutes with tensoring by a module on the original
site, naturally in the module on the slice site. -/
@[stacks 0E8I]
noncomputable def extensionByZeroTensorIso (F : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    letI := Stacks.Sites.ExtensionByZero.sheafRestrictionIsRightAdjoint X.J (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U
    let E := _root_.SheafOfModules.pullback.{u}
      (F := Over.forget U) (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))
    E ⋙ ((sheafTensor.{u, u, u, u, u} X.O).obj F) ≅
      ((sheafTensor.{u, u, u, u, u} (X.O.over U)).obj (F.over U)) ⋙ E := by
  letI := Stacks.Sites.ExtensionByZero.sheafRestrictionIsRightAdjoint X.J (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U
  let E := _root_.SheafOfModules.pullback.{u}
    (F := Over.forget U) (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))
  let adjE := _root_.SheafOfModules.pullbackPushforwardAdjunction
    (F := Over.forget U) (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))
  let adjSource := adjE.comp (sheafTensorHomAdjunction X.J X.O F)
  let adjTarget := (sheafTensorHomAdjunction (X.J.over U) (X.O.over U) (F.over U)).comp adjE
  let adjSource' := adjSource.ofNatIsoRight (internalHomRestrictionNatIso X U F)
  exact adjSource'.leftAdjointUniq adjTarget

omit [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify (X.J.over U) AddCommGrpCat.{u}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **Stacks 0E8H** is natural in the source module: precomposing by `φ : F ⟶ F'` before
restricting to `C/U` is restricting and then precomposing by `φ|_U`. -/
theorem internalHomRestrictionNatIso_naturality
    {F F' : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (φ : F ⟶ F') :
    Functor.whiskerRight (internalHomSecondFunctorMapLeft X.J X.O φ)
          (_root_.SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O) U) ≫
        (internalHomRestrictionNatIso X U F).hom =
      (internalHomRestrictionNatIso X U F').hom ≫
        Functor.whiskerLeft (_root_.SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O) U)
          (internalHomSecondFunctorMapLeft (X.J.over U) (X.O.over U) (φ.over U)) := by
  ext H
  rfl

/-- Extension by zero from the localized site `C/U`: the left adjoint of restriction. -/
noncomputable def extensionByZeroFunctor :
    _root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) ⥤ _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  letI := Stacks.Sites.ExtensionByZero.sheafRestrictionIsRightAdjoint X.J (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U
  _root_.SheafOfModules.pullback.{u} (F := Over.forget U) (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))

/-- Extension by zero is left adjoint to restriction to the localized site `C/U`, with the
right adjoint written as `SheafOfModules.overFunctor`. -/
@[sga "4 IV 11.3.1" "special case", sga "4 IV 14.2" "j_! ⊣ j^*"]
noncomputable def extensionByZeroAdjunction :
    extensionByZeroFunctor X U ⊣
      _root_.SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O) U :=
  letI := Stacks.Sites.ExtensionByZero.sheafRestrictionIsRightAdjoint X.J (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U
  _root_.SheafOfModules.pullbackPushforwardAdjunction
    (F := Over.forget U) (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))

/-- `F ↦ (G ↦ E(G) ⊗_O F)`: tensoring by a module on the big site, precomposed with extension
by zero from the localized site. -/
noncomputable def extensionTensorBifunctor :
    _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⥤
      _root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) ⥤ _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  sheafTensor.{u, u, u, u, u} X.O ⋙ (Functor.whiskeringLeft _ _ _).obj (extensionByZeroFunctor X U)

/-- `F ↦ (G ↦ E(G ⊗_{O|_U} F|_U))`: tensoring by the restriction of a module on the big site,
followed by extension by zero. -/
noncomputable def tensorExtensionBifunctor :
    _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⥤
      _root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) ⥤ _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  _root_.SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O) U ⋙
    sheafTensor.{u, u, u, u, u} (X.O.over U) ⋙
      (Functor.whiskeringRight _ _ _).obj (extensionByZeroFunctor X U)

/-- Extension by zero followed by tensoring by `F` is left adjoint to restriction followed by
internal Hom out of `F|_U`: the tensor--internal-Hom adjunction composed with extension by
zero, with its right adjoint corrected by Stacks 0E8H. -/
noncomputable def extensionTensorAdjunction
    (F : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (extensionTensorBifunctor X U).obj F ⊣
      _root_.SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O) U ⋙
        internalHomSecondFunctor (X.J.over U) (X.O.over U) (F.over U) :=
  ((extensionByZeroAdjunction X U).comp
    (sheafTensorHomAdjunction X.J X.O F)).ofNatIsoRight (internalHomRestrictionNatIso X U F)

/-- Tensoring by `F|_U` on the localized site followed by extension by zero is left adjoint to
the same functor: the tensor--internal-Hom adjunction on `C/U` composed with extension by
zero. -/
noncomputable def tensorExtensionAdjunction
    (F : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (tensorExtensionBifunctor X U).obj F ⊣
      _root_.SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O) U ⋙
        internalHomSecondFunctor (X.J.over U) (X.O.over U) (F.over U) :=
  (sheafTensorHomAdjunction (X.J.over U) (X.O.over U) (F.over U)).comp
    (extensionByZeroAdjunction X U)

/-- The two adjunctions behind Stacks 0E8I are compatible with maps of the module on the big
site: the conjugate of tensoring by `φ` is the conjugate of tensoring by `φ|_U`. -/
theorem conjugateEquiv_extensionTensor_naturality
    {F F' : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (φ : F ⟶ F') :
    conjugateEquiv
        (((extensionByZeroAdjunction X U).comp
          (sheafTensorHomAdjunction X.J X.O F')).ofNatIsoRight
            (internalHomRestrictionNatIso X U F'))
        (((extensionByZeroAdjunction X U).comp
          (sheafTensorHomAdjunction X.J X.O F)).ofNatIsoRight
            (internalHomRestrictionNatIso X U F))
        (Functor.whiskerLeft (extensionByZeroFunctor X U) ((sheafTensor.{u, u, u, u, u} X.O).map φ)) =
      conjugateEquiv
        ((sheafTensorHomAdjunction (X.J.over U) (X.O.over U) (F'.over U)).comp
          (extensionByZeroAdjunction X U))
        ((sheafTensorHomAdjunction (X.J.over U) (X.O.over U) (F.over U)).comp
          (extensionByZeroAdjunction X U))
        (Functor.whiskerRight ((sheafTensor.{u, u, u, u, u} (X.O.over U)).map (φ.over U))
          (extensionByZeroFunctor X U)) := by
  refine (conjugateEquiv_ofNatIsoRight _ _ _ _ _).trans ?_
  refine (congrArg (fun k => (internalHomRestrictionNatIso X U F').inv ≫ k ≫
    (internalHomRestrictionNatIso X U F).hom)
      (conjugateEquiv_whiskerLeft (sheafTensorHomAdjunction X.J X.O F')
        (sheafTensorHomAdjunction X.J X.O F) (extensionByZeroAdjunction X U)
        ((sheafTensor.{u, u, u, u, u} X.O).map φ))).trans ?_
  refine (congrArg (fun k => (internalHomRestrictionNatIso X U F').inv ≫
    Functor.whiskerRight k (_root_.SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O) U) ≫
      (internalHomRestrictionNatIso X U F).hom)
        (conjugateEquiv_sheafTensor_map X.J X.O φ)).trans ?_
  refine ((Iso.inv_comp_eq _).2 (internalHomRestrictionNatIso_naturality X U φ)).trans ?_
  refine (congrArg (fun k => Functor.whiskerLeft
    (_root_.SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O) U) k)
      (conjugateEquiv_sheafTensor_map (X.J.over U) (X.O.over U) (φ.over U)).symm).trans ?_
  exact (conjugateEquiv_whiskerRight
    (sheafTensorHomAdjunction (X.J.over U) (X.O.over U) (F'.over U))
    (sheafTensorHomAdjunction (X.J.over U) (X.O.over U) (F.over U))
    (extensionByZeroAdjunction X U)
    ((sheafTensor.{u, u, u, u, u} (X.O.over U)).map (φ.over U))).symm

/-- Stacks 0E8I is uniqueness of left adjoints for `extensionTensorAdjunction` and
`tensorExtensionAdjunction`. -/
theorem extensionTensorBifunctorIsoApp_eq_leftAdjointUniq
    (F : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    extensionByZeroTensorIso X U F =
      Adjunction.leftAdjointUniq (extensionTensorAdjunction X U F)
        (tensorExtensionAdjunction X U F) :=
  rfl

/-- **Stacks 0E8I** is natural in the module on the big site. -/
theorem extensionTensorBifunctorIsoApp_naturality
    {F F' : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (φ : F ⟶ F') :
    (extensionTensorBifunctor X U).map φ ≫ (extensionByZeroTensorIso X U F').hom =
      (extensionByZeroTensorIso X U F).hom ≫ (tensorExtensionBifunctor X U).map φ :=
  leftAdjointUniq_naturality_of_eq _ _ _ _ _ _
    (extensionTensorBifunctorIsoApp_eq_leftAdjointUniq X U F)
    (extensionTensorBifunctorIsoApp_eq_leftAdjointUniq X U F') _ _
    (conjugateEquiv_extensionTensor_naturality X U φ)

/-- **Stacks 0E8I, bifunctorial form.** Extension by zero commutes with tensoring by a module
on the original site, naturally in the module on the slice site *and* in the module on the
original site. -/
@[stacks 0E8I "bifunctorial form"]
noncomputable def extensionTensorBifunctorIso :
    extensionTensorBifunctor X U ≅ tensorExtensionBifunctor X U :=
  NatIso.ofComponents (extensionByZeroTensorIso X U)
    (fun φ => extensionTensorBifunctorIsoApp_naturality X U φ)

end Restriction

end Stacks.SheafOfModules.ExtensionByZero

end
