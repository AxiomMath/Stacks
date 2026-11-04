module

public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.InternalHomEvaluationRestriction
public import StacksFrontier.CategoryTheory.Sites.Modules.LocalizationRingedSites.PullbackToposSquare

/-!
# Transporting the two factors of a tensor product along Stacks 04IX

Let `(C, O)` be a ringed site and `U` an object of `C`. Stacks 04IX identifies the pullback of
sheaves of modules along the localization morphism of ringed topoi at `U` with restriction to the
slice site; `AlgebraicGeometry.RingedSite.localizationPullbackToposIsoRestriction` is that
identification at the two-field morphism of ringed topoi, which is the spelling the comparison of
Stacks 03EL is stated over.

A statement comparing a tensor product of *pullbacks* with a tensor product of *restrictions*
therefore has to move that identification into each of the two tensor factors in turn. This file
names that composite, so that the two halves of such a comparison — the chain of Stacks 03EL on
one side, the mate of Stacks 0E8H on the other — are stated about one and the same term rather
than about two inlined copies of it that would then need a bridge.

The two factors are moved by the two *one-variable* functorial actions of the curried tensor
product of Stacks 0GMW, `Stacks.SheafOfModules.Tensor.sheafTensor`, and not by the action of the
bifunctor of Stacks 03EL on a pair: that is the spelling the mate of Stacks 0E8H is stated at,
and keeping to it is what lets the comparison be assembled without forcing the curried tensor
product against the bifunctor inside a hand-written type.

## Main definitions

* `Stacks.SheafOfModules.tensorTransportFirst` and
  `Stacks.SheafOfModules.tensorTransportSecond`: the two one-variable actions, named. A statement
  about the transport is written at their composite; see their docstrings for why.
* `Stacks.SheafOfModules.localizationTensorTransport`: the transport
  `π^*A ⊗_{O|_U} π^*F ⟶ A|_U ⊗_{O|_U} F|_U` of the two tensor factors along Stacks 04IX.

## References

* [Stacks Project, Tag 04IX](https://stacks.math.columbia.edu/tag/04IX)
* [Stacks Project, Tag 0GMW](https://stacks.math.columbia.edu/tag/0GMW)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.SheafOfModules.Tensor (sheafTensor)

namespace Stacks.SheafOfModules

universe u

open Stacks.SheafOfModules.InternalHom

section TensorTransport

variable (X : RingedSite.{u, u, u}) (U : X.C)
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(X.J.over U).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget RingCat.{u})]
  [(X.J.over U).HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [(X.J.over U).HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify (X.J.over U) AddCommGrpCat.{u}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  (A F : _root_.SheafOfModules.{u} (Tensor.ringSheaf X.O))

/-- **The transport of the first tensor factor.** The one-variable functorial action of the
curried tensor product of Stacks 0GMW on a morphism `φ` into `A|_U`, evaluated at a second
factor `F'`. -/
def tensorTransportFirst
    {A' : _root_.SheafOfModules.{u} (Tensor.ringSheaf (X.O.over U))} (φ : A' ⟶ A.over U)
    (F' : _root_.SheafOfModules.{u} (Tensor.ringSheaf (X.O.over U))) :
    ((sheafTensor (X.O.over U)).obj A').obj F' ⟶
      ((sheafTensor (X.O.over U)).obj (A.over U)).obj F' :=
  ((sheafTensor (X.O.over U)).map φ).app F'

/-- **The transport of the second tensor factor.** The one-variable functorial action on a
morphism `ψ` into `F|_U` of the curried tensor product of Stacks 0GMW with first factor `A|_U`. -/
def tensorTransportSecond
    {F' : _root_.SheafOfModules.{u} (Tensor.ringSheaf (X.O.over U))} (ψ : F' ⟶ F.over U) :
    ((sheafTensor (X.O.over U)).obj (A.over U)).obj F' ⟶
      ((sheafTensor (X.O.over U)).obj (A.over U)).obj (F.over U) :=
  ((sheafTensor (X.O.over U)).obj (A.over U)).map ψ

/-- **The transport of the two tensor factors along Stacks 04IX.** The identification of the
pullback along the localization morphism at `U` with restriction to the slice site, moved into
the first and then the second factor of a tensor product.

Both factors are moved by one-variable functorial actions of the curried tensor product of
Stacks 0GMW, which is the spelling the mate of Stacks 0E8H is stated at. Those two actions are
`tensorTransportFirst` and `tensorTransportSecond`, so that a statement about this transport can
be written at their composite -- which is what it is -- rather than at this name, which the
kernel will not convert with its own body. -/
def localizationTensorTransport :
    ((sheafTensor (X.O.over U)).obj
          ((toposPullback (X.localizationRingedToposHom U)).obj A)).obj
        ((toposPullback (X.localizationRingedToposHom U)).obj F) ⟶
      ((sheafTensor (X.O.over U)).obj (A.over U)).obj (F.over U) :=
  tensorTransportFirst X U A ((X.localizationPullbackToposIsoRestriction U).hom.app A)
      ((toposPullback (X.localizationRingedToposHom U)).obj F) ≫
    tensorTransportSecond X U A F ((X.localizationPullbackToposIsoRestriction U).hom.app F)

end TensorTransport

end Stacks.SheafOfModules

end
