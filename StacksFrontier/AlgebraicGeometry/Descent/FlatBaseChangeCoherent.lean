module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import StacksFrontier.AlgebraicGeometry.AffinePushforward.BaseChange
public import StacksFrontier.AlgebraicGeometry.Descent.FlatBaseChange

/-!
# The intersection of a module with the pushforward of a submodule of its pullback

Let `f : Y ⟶ X` be a morphism of schemes, let `F` be a module on `X`, let `G` be a module on `Y`
and let `φ : G ⟶ f^* F`.  Following
[Stacks, Tag 07TT](https://stacks.math.columbia.edu/tag/07TT), the *intersection*
`F ∩ f_* G` is the fibre product of
`F ⟶ f_* f^* F ⟵ f_* G`,
the first leg being the unit of `f^* ⊣ f_*` and the second `f_*` applied to `φ`.  Tag 07TT says
that this intersection is coherent when `f` is flat, surjective, quasi-compact and
quasi-separated, `X` and `Y` are locally Noetherian, `φ` is injective and `G` is coherent.

This file sets up that intersection and the two inputs to the proof of Tag 07TT that do not
depend on the theory of coherent modules:

* the base-change morphism `f^* f_* G ⟶ p_* q^* G` for the square cut out by the two
  projections `p, q : Y ×_X Y ⟶ Y`, whose invertibility is exactly what
  [Stacks, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH) provides, and
* the fact that `p` has a section, namely the diagonal, which is the step the source refers to as
  "since `p` has a section we win".

## Main definitions

* `Stacks.Modules.selfBaseChange` is the base-change morphism `f^* f_* G ⟶ p_* q^* G` attached to
  the square of the two projections of `Y ×_X Y`.
* `Stacks.Modules.inter` is the intersection `F ∩ f_* G`, and
  `Stacks.Modules.interι`, `Stacks.Modules.interToPushforward` are its two legs.

## Main results

* `Stacks.Modules.selfBaseChange_naturality` is the naturality square of `selfBaseChange`, which
  is what transports a map of modules on `Y` through the comparison.
* `Stacks.Modules.isSplitEpi_pullback_fst` says the first projection of `Y ×_X Y` is a split
  epimorphism, split by the diagonal.
* `Stacks.Modules.mono_interι` says the intersection is a submodule of `F` as soon as `φ` is a
  monomorphism.
* `Stacks.Modules.pullbackInterIso` identifies `f^* (F ∩ f_* G)` with
  `f^* F ∩ f^* f_* G`, under the hypothesis that `f^*` preserves fibre products.  This is the
  first step of the proof of Tag 07TT, where that hypothesis comes from flatness of `f`.

## Implementation notes

`Stacks.Modules.pullbackInterIso` takes `f^*` preserving pullbacks as a hypothesis rather than
deriving it from `AlgebraicGeometry.Flat`: exactness of the pullback of sheaves of modules along
a flat morphism of schemes is not available, and is a separate piece of work.  Stating the
hypothesis as `CategoryTheory.Limits.PreservesLimitsOfShape
CategoryTheory.Limits.WalkingCospan` keeps the lemma usable the moment it becomes available.

Everything here is stated for `AlgebraicGeometry.Scheme.Modules`, matching the formulation of
Tag 07TT, and no declaration crosses to `SheafOfModules`.

## References

* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 07TT](https://stacks.math.columbia.edu/tag/07TT)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

universe u

namespace Stacks.Modules

variable {X Y : Scheme.{u}} (f : Y ⟶ X)

/-- The two projections `p, q : Y ×_X Y ⟶ Y` form a commutative square over `f`, in the
orientation `q ≫ f = p ≫ f` required by
`Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans`. -/
theorem snd_comp_self (f : Y ⟶ X) :
    Limits.pullback.snd f f ≫ f = Limits.pullback.fst f f ≫ f :=
  Limits.pullback.condition.symm

/-- The base-change morphism `f^* f_* G ⟶ p_* q^* G` for the square of the two projections
`p = pullback.fst`, `q = pullback.snd` of `Y ×_X Y`.  [Stacks, Tag 02KH] asserts that this is an
isomorphism when `f` is flat, quasi-compact and quasi-separated and `G` is quasi-coherent; it is
in that form that Tag 02KH enters the proof of Tag 07TT. -/
def selfBaseChange (G : Y.Modules) :
    (Scheme.Modules.pullback f).obj ((Scheme.Modules.pushforward f).obj G) ⟶
      (Scheme.Modules.pushforward (Limits.pullback.fst f f)).obj
        ((Scheme.Modules.pullback (Limits.pullback.snd f f)).obj G) :=
  (Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans (snd_comp_self f)).app G

/-- Naturality of `Stacks.Modules.selfBaseChange` in the module on `Y`. -/
theorem selfBaseChange_naturality {G G' : Y.Modules} (ψ : G ⟶ G') :
    (Scheme.Modules.pullback f).map ((Scheme.Modules.pushforward f).map ψ) ≫
        selfBaseChange f G' =
      selfBaseChange f G ≫ (Scheme.Modules.pushforward (Limits.pullback.fst f f)).map
        ((Scheme.Modules.pullback (Limits.pullback.snd f f)).map ψ) :=
  (Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans
    (snd_comp_self f)).naturality ψ

/-- The first projection `Y ×_X Y ⟶ Y` is a split epimorphism, split by the diagonal.  This is
the step of the proof of Tag 07TT that reduces the general case to the case of a morphism with a
section. -/
instance isSplitEpi_pullback_fst : IsSplitEpi (Limits.pullback.fst f f) :=
  IsSplitEpi.mk' ⟨Limits.pullback.diagonal f, by simp⟩

/-- The second projection `Y ×_X Y ⟶ Y` is a split epimorphism, split by the diagonal. -/
instance isSplitEpi_pullback_snd : IsSplitEpi (Limits.pullback.snd f f) :=
  IsSplitEpi.mk' ⟨Limits.pullback.diagonal f, by simp⟩

variable (F : X.Modules) {G : Y.Modules} (φ : G ⟶ (Scheme.Modules.pullback f).obj F)

/-- The intersection `F ∩ f_* G` of Tag 07TT: the fibre product of the unit
`F ⟶ f_* f^* F` of `f^* ⊣ f_*` and the pushforward `f_* G ⟶ f_* f^* F` of `φ`. -/
def inter : X.Modules :=
  Limits.pullback ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app F)
    ((Scheme.Modules.pushforward f).map φ)

/-- The leg `F ∩ f_* G ⟶ F` of the intersection. -/
def interι : inter f F φ ⟶ F :=
  Limits.pullback.fst _ _

/-- The leg `F ∩ f_* G ⟶ f_* G` of the intersection. -/
def interToPushforward : inter f F φ ⟶ (Scheme.Modules.pushforward f).obj G :=
  Limits.pullback.snd _ _

/-- The defining square of the intersection commutes. -/
theorem interι_comp_unit :
    interι f F φ ≫ (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app F =
      interToPushforward f F φ ≫ (Scheme.Modules.pushforward f).map φ :=
  Limits.pullback.condition

/-- When `φ` is a monomorphism the intersection is a submodule of `F`: its leg to `F` is a
monomorphism, because pushforward is a right adjoint and so preserves monomorphisms, and a
pullback of a monomorphism is a monomorphism. -/
instance mono_interι [Mono φ] : Mono (interι f F φ) :=
  inferInstanceAs (Mono (Limits.pullback.fst _ _))

/-- `f^* (F ∩ f_* G) ≅ f^* F ∩ f^* f_* G`, for an `f` whose pullback functor preserves fibre
products.  In the proof of Tag 07TT the hypothesis is supplied by flatness of `f`. -/
def pullbackInterIso
    [PreservesLimitsOfShape WalkingCospan (Scheme.Modules.pullback f)] :
    (Scheme.Modules.pullback f).obj (inter f F φ) ≅
      Limits.pullback
        ((Scheme.Modules.pullback f).map
          ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app F))
        ((Scheme.Modules.pullback f).map ((Scheme.Modules.pushforward f).map φ)) :=
  PreservesPullback.iso _ _ _

end Stacks.Modules

end
