module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.TensorHomAdjunctionFreeUniverse
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InternalHomVariance
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
import StacksCore.Tactic.StacksAttribute

/-!
# The tensor--internal-Hom adjunction for sheaves of modules, at a free ring universe

Let `O` be a sheaf of commutative rings on a site `(C, J)` and let `G` be a sheaf of
`O`-modules.  For sheaves of `O`-modules `F`, `H`, morphisms out of the sheaf tensor product
are canonically identified with morphisms into the internal Hom sheaf of Stacks 03EM,

`Hom(F ⊗_O G, H) = Hom(F, Hom_O(G, H))`,

naturally in `F` and in `H`: tensoring on the right by `G` is left adjoint to internal Hom out
of `G`.  This file proves the sheaf clause of Stacks 03EO **with the universe `w` of the
sections of `O` independent of the universes `u`, `v` of the site**, the modules being at
`max u v w`.

`Stacks.SheafOfModules.InternalHom.sheafTensorRightHomAdjunction`
(`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorHomAdjunction.lean`) is the same clause at
ring universe `max u v`.  The small Zariski and small étale sites of a scheme are
`AlgebraicGeometry.RingedSite.{u + 1, u, u}`, where `max (u + 1) u = u + 1 ≠ u`, so they are
out of reach of that statement; on such a site the adjunction below applies at module universe
`u + 1`, which is where `AlgebraicGeometry.RingedSite.internalHomSheaf` of two `u`-small modules
lives.

The tensor product is the canonical one, `Stacks.SheafOfModules.Tensor.sheafTensor`, read with
its right factor fixed.  The construction is the presheaf clause
`Stacks.PresheafOfModules.InternalHom.FreeUniverse.presheafTensorHomAdjunction` composed with
the sheafification adjunction and restricted along the fully faithful forgetful functor from
sheaves of modules; the internal Hom of Stacks 03EM is already a sheaf, so the right adjoint of
the composite takes values in sheaves on the nose, and both comparison isomorphisms of
`CategoryTheory.Adjunction.restrictFullyFaithful` are `Iso.refl`.

## Main results

* `Stacks.SheafOfModules.InternalHom.FreeUniverse.sheafTensorRightHomAdjunction` and
  `sheafTensorHomEquiv`: the sheaf clause of Stacks 03EO at a free ring universe.
* `Stacks.SheafOfModules.InternalHom.FreeUniverse.sheafTensorHomEquiv_apply`: on sections the
  correspondence is the usual currying formula, which pins it down.

## References

* [Stacks Project, Tag 03EO](https://stacks.math.columbia.edu/tag/03EO)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
-/

@[expose] public section

open CategoryTheory
open Stacks.PresheafOfModules.InternalHom

open scoped TensorProduct

noncomputable section

universe w v u

namespace Stacks.SheafOfModules.InternalHom.FreeUniverse

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (R : Sheaf J CommRingCat.{w})
  [HasWeakSheafify J AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]

/-- **The sheafification adjunction for sheaves of modules, in the forgetful spelling**, at
module universe `max u v w` over a ring sheaf in an independent universe `w`.  The right adjoint
of `PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)` is the forgetful functor composed with
restriction of scalars along an identity, which is the identity functor definitionally; this
declaration is the one place where that identification is made. -/
def sheafifyForgetAdjunction :
    PresheafOfModules.sheafification.{max u v w}
        (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)
        (R := Stacks.SheafOfModules.Tensor.ringSheaf R)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj) ⊣
      _root_.SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf R) :=
  PresheafOfModules.sheafificationAdjunction (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)

variable (F G H : _root_.SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf R))

/-- **Stacks 03EO, sheaf case, at a free ring universe.**  Tensoring on the right by `G` is left
adjoint to the internal-Hom functor with source `G`, for a sheaf of rings whose sections lie in
a universe independent of those of the site.

The presheaf clause
`Stacks.PresheafOfModules.InternalHom.FreeUniverse.presheafTensorHomAdjunction` is composed
with the sheafification adjunction and the result restricted along the fully faithful forgetful
functor; this is legitimate because the right adjoint of the composite already takes values in
sheaves, the internal Hom of Stacks 03EM being a sheaf as soon as its target is. -/
@[stacks 03EO "sheaf_tensor_hom_adjunction, with the universe of the sections of the structure \
sheaf independent of the universes of the site"]
def sheafTensorRightHomAdjunction :
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max u v w, max u v w} R).flip.obj G ⊣
      internalHomSecondFunctor.{v, u, w, w} J R G :=
  Adjunction.restrictFullyFaithful
    ((FreeUniverse.presheafTensorHomAdjunction R.obj G.val).comp (sheafifyForgetAdjunction R))
    (_root_.SheafOfModules.fullyFaithfulForget _) (Functor.FullyFaithful.id _)
    (Iso.refl _) (Iso.refl _)

/-- **Stacks 03EO, sheaf case, at a free ring universe, as displayed.**  The canonical
tensor--internal-Hom correspondence `Hom(F ⊗_O G, H) = Hom(F, Hom_O(G, H))` on sheaves of
modules, as the hom-equivalence of `sheafTensorRightHomAdjunction`. -/
def sheafTensorHomEquiv :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max u v w, max u v w} R).obj F).obj G ⟶
        H) ≃
      (F ⟶ (internalHomSecondFunctor.{v, u, w, w} J R G).obj H) :=
  (sheafTensorRightHomAdjunction R G).homEquiv F H

/-- The hom-equivalence of `sheafifyForgetAdjunction` is the sheafification unit followed by
the given morphism of sheaves. -/
lemma sheafifyForgetAdjunction_homEquiv
    (P : _root_.PresheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)
    (f : (PresheafOfModules.sheafification.{max u v w}
        (R := Stacks.SheafOfModules.Tensor.ringSheaf R)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)).obj P ⟶ H) :
    (sheafifyForgetAdjunction R).homEquiv P H f =
      (sheafifyForgetAdjunction R).unit.app P ≫ f.val :=
  (sheafifyForgetAdjunction R).homEquiv_unit P H f

/-- **Stacks 03EO, sheaf case, at a free ring universe, on sections.**  The correspondence is
the canonical currying map: a morphism `b` out of the sheafified tensor product is sent to the
map taking a section `x` of `F` over `U` and a section `y` of `G` over `T ⟶ U` to the value of
`b` on the image of the pure tensor `x|_T ⊗ y`. -/
@[stacks 03EO "sheaf_tensor_hom_adjunction, with the universe of the sections of the structure \
sheaf independent of the universes of the site"]
theorem sheafTensorHomEquiv_apply
    (b : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max u v w, max u v w} R).obj
      F).obj G ⟶ H) (U : C)
    (x : F.val.obj (Opposite.op U)) {T : C} (q : T ⟶ U)
    (y : G.val.obj (Opposite.op T)) :
    FreeUniverse.sectionOfRestr R.obj H.val U q
        (((((sheafTensorHomEquiv R F G H b).val.app (Opposite.op U)).hom x).app
          (Opposite.op (Over.mk q))).hom (FreeUniverse.restrSection R.obj G.val U q y)) =
      FreeUniverse.globalTensorHom R.obj F.val G.val H.val
        ((sheafifyForgetAdjunction R).homEquiv (F.val.tensorObj G.val) H b) T
        (F.val.restrictₛₗ q.op x ⊗ₜ y) :=
  FreeUniverse.presheafTensorHomEquiv_apply R.obj F.val G.val H.val
    ((sheafifyForgetAdjunction R).homEquiv (F.val.tensorObj G.val) H b) U x q y

end Stacks.SheafOfModules.InternalHom.FreeUniverse

end
