module

public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier
public import StacksFrontier.AlgebraicGeometry.InvertibleBridge.Basic
public import StacksFrontier.AlgebraicGeometry.InvertibleDual.Evaluation
public import StacksFrontier.AlgebraicGeometry.ModulePullbackPseudofunctor.Basic
public import StacksFrontier.AlgebraicGeometry.PullbackTensor.Basic
public import StacksFrontier.AlgebraicGeometry.PullbackTensor.StalkFormula
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHom
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.InternalHomVariance
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import StacksFrontier.AlgebraicGeometry.Conormal.Charts
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The normal sheaf of an effective Cartier divisor

Let `S` be a scheme and `D ⊆ S` an effective Cartier divisor, so that the ideal sheaf `ℐ_D`
is an invertible `𝒪_S`-module and `𝒪_S(D) = SheafHom(ℐ_D, 𝒪_S)`. Tag 0B3P asserts that the
conormal sheaf of `D` in `S` is `ℐ_D|_D = 𝒪_S(-D)|_D` and that the normal sheaf is
`𝒪_S(D)|_D`.

The conormal sheaf of an immersion `i : Z ⟶ X` is, by Tag 01R2, the pullback along the
closed immersion `i.liftCoborder : Z ⟶ i.coborderRange` of the ideal sheaf of that closed
immersion; the normal sheaf is its dual. The conormal clause of Tag 0B3P is therefore the
independence of that construction from the open through which the immersion factors, which
for a *closed* immersion is proved here in full: the open is the whole target and its open
immersion is an isomorphism, so `Stacks.ClosedImmersion.pullbackIdealSheafIso` applies. The
normal clause is the further statement that the dual commutes with the pullback of an
invertible module sheaf, which is Tag 01CD at one pair; that tag is now available outright
(`Stacks.RingedSpace.isIso_comparison`), so the normal clause too is proved here with no
hypothesis.

## Main definitions

* `Stacks.SheafOfModules.internalHomIsoLeft`, `Stacks.SheafOfModules.sheafHomIsoLeft` and
  `Stacks.SheafOfModules.dualSheafIso`: the sheaf-hom, and in particular the dual, of a
  sheaf of modules transports along an isomorphism of its first argument.
* `Stacks.Divisors.normalSheaf`: the normal sheaf of an immersion, the dual of its conormal
  sheaf.

## Main results

* `Stacks.Divisors.coborderRange_eq_top` and `Stacks.Divisors.isIso_coborderRange_ι`: for a
  closed immersion the canonical open through which Tag 01R2 factors it is the whole target,
  and the open immersion of that open is an isomorphism. This is the geometric half of
  Tag 01R3 (1) in the case of a closed immersion.
* `Stacks.Divisors.conormalSheafIsoNegativeTwist`: Tag 0B3P's conormal-sheaf clause,
  unconditionally.
* `Stacks.Divisors.dualPullbackIso`: the dual of a pullback is the pullback of the dual, for
  a module sheaf on a ringed space with local stalks, given the trivializing pairing of the
  pulled-back dual against the pullback;
  `Stacks.Divisors.dualPullbackIsoOfPullbackStalkFormula` is the same with that pairing
  derived from the stalk formula of Tag 0098.
* `Stacks.Divisors.normalSheafIsoInvertibleSheaf`: Tag 0B3P's normal-sheaf clause,
  unconditionally.

## Implementation notes

**The conormal clause.** `Stacks.Divisors.coborderRange_eq_top` says the canonical open of
Tag 01R2 is the whole target when the immersion is closed, so its open immersion is an
isomorphism of schemes, hence of ringed spaces. The transport of the ideal sheaf and of the
pullback along such an isomorphism is
`StacksFrontier/AlgebraicGeometry/PullbackPseudofunctor/Basic.lean`, and nothing else is
needed: the sheaf `𝒪_X(-D)` of Tag 01WX *is* the ideal sheaf, so the right-hand side states
both of Tag 0B3P's descriptions of the conormal sheaf at once.

**The normal clause, and what is unconditional in it.** The dual transports along an
isomorphism of its argument, and the dual of `f^* ℐ_D` is identified with the pullback
`f^* (ℐ_D^∨)` by the two being tensor inverses of one and the same invertible module sheaf.
The first is new: the internal hom of Tag 03EM is contravariantly functorial in its first
argument by `Stacks.PresheafOfModules.InternalHom.internalHomFunctor`, and
`Stacks.SheafOfModules.sheafHom` has that presheaf as its underlying presheaf, so the
transport is obtained by packaging the image of an isomorphism under that functor as a
morphism of sheaves of modules. The second is `Stacks.SheafOfModules.isoOfTensorIsoUnit`,
which reads off the autoequivalence that invertibility provides and is therefore determined
by the two pairings, not an arbitrary isomorphism of the two sheaves. That `f^* ℐ_D` *is*
invertible, and that its dual is one of the two tensor inverses, are not hypotheses either:
the first is Tag 0B8K (2) ⟹ (1) applied to the pairing
(`Stacks.SheafOfModules.isInvertible_of_tensorIsoUnit`) and the second is the evaluation
pairing of `StacksFrontier/AlgebraicGeometry/InvertibleDual/Evaluation.lean`, which is an
isomorphism for an invertible module sheaf on a scheme.

**Tag 01CD, which used to be the one hypothesis.** `Stacks.RingedSpace.PullbackStalkFormula`
for the closed immersion of `D` — that is Tag 0098 for `modulePullback` at universe `u` — was
carried here as a named hypothesis for as long as it was unproved. It is now a theorem,
`Stacks.RingedSpace.pullbackStalkFormula`, so Tag 01CD is available outright as
`Stacks.RingedSpace.isIso_comparison`, and that is what turns the evaluation pairing of `ℐ_D`
into the pairing of `f^* (ℐ_D^∨)` against `f^* ℐ_D` through
`Stacks.RingedSpace.tensorIsoUnitPullback`. `dualPullbackIsoOfPullbackStalkFormula` keeps the
predicate as an explicit argument, because it is the general statement for an arbitrary
morphism of ringed spaces with local stalks; `normalSheafIsoInvertibleSheaf` supplies it.

**Which `IsInvertible`.** `Stacks.SheafOfModules.IsInvertible` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorInvertible.lean`, which is the class in
which Tags 0B8K and 0B8M are stated and the one the evaluation pairing and the tensor-inverse
uniqueness used below are stated for. The statement of `normalSheafIsoInvertibleSheaf` names
neither copy: its only occurrence of either is the statement's own
`[IsEffectiveCartierDivisor D]` binder, which is stated in terms of
`AlgebraicGeometry.SheafOfModules.IsInvertible`. Inside the proof the witness is moved across
by `Stacks.InvertibleBridge.stacksIsInvertible_of_algebraicGeometryIsInvertible`, the
canonical bridge, because the evaluation pairing of `ℐ_D` on `X` is now needed and that is
stated for the other copy.

**Naming.** `Stacks.Divisors.normalSheaf` is stated for an arbitrary immersion, as the
Stacks Project states it, rather than only for an effective Cartier divisor. Its conormal
argument is written out rather than abbreviated, and so is `𝒪_X(D)` in the statement of
`normalSheafIsoInvertibleSheaf`; both do have names, in modules this one does not import.
The conormal sheaf of Tag 01R2 is `Stacks.Conormal.conormalSheaf` of
`StacksFrontier/AlgebraicGeometry/ConormalComparison/IdealSheafComparison.lean`, where that tag's
construction clause is registered, and it is the same construction written out here; `𝒪_X(D)` is
`Stacks.Divisors.invertibleSheaf` of
`StacksFrontier/AlgebraicGeometry/Divisors/InvertibleSheaf.lean`, where part (1) of Tag 01WX is
registered, and again the same term.

## References

* [Stacks Project, Tag 0B3P](https://stacks.math.columbia.edu/tag/0B3P)
* [Stacks Project, Tag 01R2](https://stacks.math.columbia.edu/tag/01R2)
* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
* [Stacks Project, Tag 01WX](https://stacks.math.columbia.edu/tag/01WX)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CT](https://stacks.math.columbia.edu/tag/01CT)
* [Stacks Project, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 0FNV](https://stacks.math.columbia.edu/tag/0FNV)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite RingedSpaceModuleAdjunction
open Stacks.PresheafOfModules.InternalHom
open Stacks.SheafOfModules.TensorStalkRingedSpace (ringStalk)

universe v u

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v})
  (h𝒪 : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪))

/-- The internal hom presheaf of Tag 03EM transports along an isomorphism of its first
argument: it is the image of that isomorphism under the contravariant functoriality
`internalHomFunctor` in the first variable. -/
noncomputable def internalHomIsoLeft
    {F F' : SheafOfModules.{max u v} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
      h𝒪)}
    (G : SheafOfModules.{max u v} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))
      (e : F ≅ F') :
    internalHom 𝒪 F.val G.val ≅ internalHom 𝒪 F'.val G.val :=
  ((internalHomFunctor 𝒪 G.val).mapIso
    ((SheafOfModules.forget (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)).mapIso
      e.symm)).unop

/-- The sheaf-hom transports along an isomorphism of its first argument. -/
noncomputable def sheafHomIsoLeft
    {F F' : SheafOfModules.{max u v} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
      h𝒪)}
    (G : SheafOfModules.{max u v} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))
      (e : F ≅ F') :
    sheafHom 𝒪 h𝒪 F G ≅ sheafHom 𝒪 h𝒪 F' G where
  hom := { val := (internalHomIsoLeft 𝒪 h𝒪 G e).hom }
  inv := { val := (internalHomIsoLeft 𝒪 h𝒪 G e).inv }
  hom_inv_id := SheafOfModules.Hom.ext (internalHomIsoLeft 𝒪 h𝒪 G e).hom_inv_id
  inv_hom_id := SheafOfModules.Hom.ext (internalHomIsoLeft 𝒪 h𝒪 G e).inv_hom_id

/-- The dual of a sheaf of modules transports along an isomorphism. -/
noncomputable def dualSheafIso
    {F F' : SheafOfModules.{max u v} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
      h𝒪)} (e : F ≅ F') :
    dualSheaf 𝒪 h𝒪 F ≅ dualSheaf 𝒪 h𝒪 F' :=
  sheafHomIsoLeft 𝒪 h𝒪 _ e

end Stacks.SheafOfModules

namespace Stacks.Divisors

/-- The canonical open through which an immersion factors as a closed immersion is the whole
target, when the immersion is already closed. -/
alias coborderRange_eq_top := Stacks.Conormal.coborderRange_eq_top

/-- For a closed immersion the open immersion of `Scheme.Hom.coborderRange` is an
isomorphism, so the closed-immersion factorization of Tag 01R2 is the immersion itself up to
that isomorphism. -/
instance isIso_coborderRange_ι {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    IsIso i.coborderRange.ι := by
  rw [coborderRange_eq_top i, ← Scheme.topIso_hom]
  infer_instance

/-- **The normal sheaf of an immersion** `i : Z ⟶ X`: the dual of the conormal sheaf
`𝒞_{Z/X}`, which by Tag 01R2 is the pullback along `i.liftCoborder` of the ideal sheaf of
that closed immersion. -/
noncomputable abbrev normalSheaf {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] :
    SheafOfModules.{u} (structureSheafRing Z.toRingedSpace) :=
  Stacks.SheafOfModules.dualSheaf Z.sheaf.obj (structureSheafRing Z.toRingedSpace).property
    ((modulePullback i.liftCoborder.toLRSHom.toShHom).obj
      (Stacks.ClosedImmersion.idealSheaf i.liftCoborder.toLRSHom.toShHom))

/-- **The dual of a pullback is the pullback of the dual**, for a module sheaf whose pulled-back
dual pairs trivially with the pullback, on a ringed space whose structure-sheaf stalks are local
rings.

The pairing `hpullbackPair` makes `f^* L` invertible by Tag 0B8K (2) ⟹ (1), and then the
evaluation pairing of `f^* L` with *its* dual is an isomorphism as well
(`Stacks.SheafOfModules.evaluationIsoOfIsInvertible`, Tag 01CT (2) on a ringed space).
So `(f^* L)^∨` and `f^* (L^∨)` are two tensor inverses of the invertible sheaf `f^* L`, and
`Stacks.SheafOfModules.isoOfTensorIsoUnit` identifies them through the autoequivalence
`· ⊗ f^* L`. The identification is therefore canonical in the pairings rather than an arbitrary
isomorphism of the two sheaves.

`hpullbackPair` is the pullback of the evaluation pairing of `L`, an isomorphism by Tag 01CT (2)
together with Tag 01CD (pullback commutes with tensor products) and
`SheafOfModules.pullbackObjUnitToUnit`. Tag 01CD is available outright for a morphism of ringed
spaces, as `Stacks.RingedSpace.isIso_comparison` of
`StacksFrontier/AlgebraicGeometry/PullbackTensor/StalkFormula.lean`, which this module imports, so
nothing here rests on it being unproved: `hpullbackPair` stays an argument only to keep this the
general statement, and `Stacks.Divisors.dualPullbackIsoOfPullbackStalkFormula` just below is the
same isomorphism with it discharged. See the implementation notes of this file. -/
noncomputable def dualPullbackIso {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    [∀ x : X.carrier, IsLocalRing (ringStalk X x)]
    (L : SheafOfModules.{u} (structureSheafRing Y))
    (hpullbackPair :
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.sheaf.obj,
          Presheaf.isSheaf_of_isSheaf_comp _ (X.sheaf.obj) (forget₂ CommRingCat RingCat)
            ((structureSheafRing X).property)⟩).obj (((modulePullback f).obj
            (Stacks.SheafOfModules.dualSheaf Y.sheaf.obj (structureSheafRing Y).property L)))).obj
          (((modulePullback f).obj L))) ≅
        SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf X.sheaf.obj
          (structureSheafRing X).property)) :
    Stacks.SheafOfModules.dualSheaf X.sheaf.obj (structureSheafRing X).property
        ((modulePullback f).obj L) ≅
      (modulePullback f).obj
        (Stacks.SheafOfModules.dualSheaf Y.sheaf.obj (structureSheafRing Y).property L) :=
  have hinv : Stacks.SheafOfModules.IsInvertible X.sheaf.obj (structureSheafRing X).property
      ((modulePullback f).obj L) :=
    Stacks.SheafOfModules.isInvertible_of_tensorIsoUnit _ _ _ _ hpullbackPair
  have : Stacks.SheafOfModules.IsInvertible X.presheaf (structureSheafRing X).property
      ((modulePullback f).obj L) := hinv
  Stacks.SheafOfModules.isoOfTensorIsoUnit _ _ _ _ _
    (Stacks.SheafOfModules.evaluationIsoOfIsInvertible (X := X) _) hpullbackPair

/-- **The dual of a pullback is the pullback of the dual**, for an invertible module sheaf on a
ringed space with local stalks, given the stalk formula of Tag 0098 for the pullback.

This is `dualPullbackIso` with its one hypothesis discharged: the trivializing pairing of `f^* L`
against `f^* (L^∨)` is the pullback of the evaluation pairing of `L`
(`Stacks.SheafOfModules.evaluationIsoOfIsInvertible`, Tag 01CT (2) on a ringed space)
along `Stacks.RingedSpace.tensorIsoUnitPullback`, whose Tag 01CD input is supplied by
`Stacks.RingedSpace.isIso_comparison_of_pullbackStalkFormula`. -/
@[ega "0 5.4.5" "special case"]
noncomputable def dualPullbackIsoOfPullbackStalkFormula {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    [∀ x : X.carrier, IsLocalRing (ringStalk X x)]
    [∀ y : Y.carrier, IsLocalRing (ringStalk Y y)]
    (hf : Stacks.RingedSpace.PullbackStalkFormula f)
    (L : SheafOfModules.{u} (structureSheafRing Y))
    [Stacks.SheafOfModules.IsInvertible Y.sheaf.obj (structureSheafRing Y).property L] :
    Stacks.SheafOfModules.dualSheaf X.sheaf.obj (structureSheafRing X).property
        ((modulePullback f).obj L) ≅
      (modulePullback f).obj
        (Stacks.SheafOfModules.dualSheaf Y.sheaf.obj (structureSheafRing Y).property L) :=
  have _hL : Stacks.SheafOfModules.IsInvertible Y.presheaf (structureSheafRing Y).property L := ‹_›
  dualPullbackIso f L
    (Stacks.RingedSpace.tensorIsoUnitPullback f
      (Stacks.SheafOfModules.dualSheaf Y.sheaf.obj (structureSheafRing Y).property L) L
      (Stacks.SheafOfModules.evaluationIsoOfIsInvertible (X := Y) L)
      (Stacks.RingedSpace.isIso_comparison_of_pullbackStalkFormula f hf _ _))

/-- **Stacks Project, Tag 0B3P**, the conormal-sheaf clause: the conormal sheaf of a closed
subscheme `D ⊆ X` is the restriction `ℐ_D|_D = 𝒪_X(-D)|_D` of its ideal sheaf.

The conormal sheaf of Tag 01R2 is computed through the `liftCoborder` factorization of the
immersion; for a closed immersion the open through which it factors is the whole target
(`coborderRange_eq_top`) and its open immersion is an isomorphism
(`isIso_coborderRange_ι`), so `Stacks.ClosedImmersion.pullbackIdealSheafIso` identifies the two
pullbacks. The sheaf `𝒪_X(-D)` of Tag 01WX is the ideal sheaf itself, so the right-hand side is
both descriptions at once. -/
@[stacks 0B3P "conormal sheaf"]
noncomputable def conormalSheafIsoNegativeTwist {X : Scheme.{u}} (D : X.IdealSheafData) :
    (modulePullback D.subschemeι.liftCoborder.toLRSHom.toShHom).obj
        (Stacks.ClosedImmersion.idealSheaf
          D.subschemeι.liftCoborder.toLRSHom.toShHom) ≅
      (modulePullback D.subschemeι.toLRSHom.toShHom).obj
        (Stacks.ClosedImmersion.idealSheaf D.subschemeι.toLRSHom.toShHom) :=
  (Stacks.ClosedImmersion.pullbackIdealSheafIso _
    D.subschemeι.coborderRange.ι.toLRSHom.toShHom D.subschemeι.toLRSHom.toShHom
    (show (D.subschemeι.liftCoborder ≫ D.subschemeι.coborderRange.ι).toLRSHom.toShHom = _ by
      rw [Scheme.Hom.liftCoborder_ι])).symm

/-- **Stacks Project, Tag 0B3P**, the normal-sheaf clause: the normal sheaf of an effective
Cartier divisor `D ⊆ X` is the restriction `𝒪_X(D)|_D` of its associated invertible sheaf
`𝒪_X(D) = SheafHom(ℐ_D, 𝒪_X)`.

There is no hypothesis beyond the divisor. The stalk formula of Tag 0098 for `modulePullback`
along the closed immersion of `D`, which used to be carried here as
`Stacks.RingedSpace.PullbackStalkFormula`, is a theorem
(`Stacks.RingedSpace.pullbackStalkFormula`), so Tag 01CD is available outright as
`Stacks.RingedSpace.isIso_comparison`. -/
@[stacks 0B3P "normal sheaf"]
noncomputable def normalSheafIsoInvertibleSheaf {X : Scheme.{u}} (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D] :
    normalSheaf D.subschemeι ≅
      (modulePullback D.subschemeι.toLRSHom.toShHom).obj
        (Stacks.SheafOfModules.dualSheaf X.sheaf.obj (structureSheafRing X.toRingedSpace).property
          (Stacks.ClosedImmersion.idealSheaf D.subschemeι.toLRSHom.toShHom)) :=
  have _h₁ : ∀ x : D.subscheme.toRingedSpace.carrier,
      IsLocalRing (ringStalk D.subscheme.toRingedSpace x) := fun x => D.subscheme.isLocalRing x
  have _h₂ : ∀ x : X.toRingedSpace.carrier, IsLocalRing (ringStalk X.toRingedSpace x) :=
    fun x => X.isLocalRing x
  have _hI : Stacks.SheafOfModules.IsInvertible X.sheaf.obj
      (structureSheafRing X.toRingedSpace).property
      (Stacks.ClosedImmersion.idealSheaf D.subschemeι.toLRSHom.toShHom) :=
    Stacks.InvertibleBridge.stacksIsInvertible_of_algebraicGeometryIsInvertible
  Stacks.SheafOfModules.dualSheafIso _ _ (conormalSheafIsoNegativeTwist D) ≪≫
    dualPullbackIsoOfPullbackStalkFormula D.subschemeι.toLRSHom.toShHom
      (Stacks.RingedSpace.pullbackStalkFormula _)
      (Stacks.ClosedImmersion.idealSheaf D.subschemeι.toLRSHom.toShHom)

end Stacks.Divisors

end
