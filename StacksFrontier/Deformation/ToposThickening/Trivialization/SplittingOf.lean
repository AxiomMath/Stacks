module

public import StacksFrontier.Deformation.RingThickening.TrivialThickening
public import StacksFrontier.Deformation.ToposThickening.Basic
public import StacksFrontier.Deformation.ToposThickening.Trivialization.AdjunctionForget
public import StacksFrontier.Deformation.ToposThickening.Trivialization.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# Splitting a trivialized first order thickening of ringed topoi

A trivialization of a first order thickening splits its structure-sheaf map. The split
square-zero extension is naturally the direct sum of the quotient structure sheaf and the kernel
ideal, with the usual square-zero product.

## Main results

* `Deformation.ToposThickening.splittingFromTrivialization` gives the sheaf-theoretic section
  and its natural square-zero-extension equivalence.

## Implementation notes

The first order thickening represents its ideal on the target topos, using the equivalence of
underlying topoi, so the splitting is stated for sheaves on the target site. The equivalence of
presheaves of rings is natural in restriction maps, hence is an equivalence of sheaves of
algebras, and its underlying kernel is the ideal represented by the thickening.

## References

* [Stacks Project, Tag 08MG](https://stacks.math.columbia.edu/tag/08MG)
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor
  pushforwardCommRingCompIso pushforwardCommRingFunctor_isEquivalence)
open Deformation.RingThickening (PresheafTrivialSquareZeroEquiv)

universe v u w v' u' w'

namespace Deformation.ToposThickening

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]

/-- A trivialization splits the structure map of a first order thickening. The natural
equivalence identifies the ring sheaf with the square-zero extension of its quotient by its
kernel. -/
@[stacks 08MG "splitting_from_trivialization"]
noncomputable def splittingFromTrivialization (i : RingedToposHom X Y)
    (hi : FirstOrderThickening i) (π : Trivialization i) :
    Σ' split : ((pushforwardCommRingFunctor i.toToposHom).obj X.O).obj ⟶ Y.O.obj,
      Σ' hs : SplitMono split,
        { _e : PresheafTrivialSquareZeroEquiv Y.O.obj
            ((pushforwardCommRingFunctor i.toToposHom).obj X.O).obj
            i.fSharp.hom split // hs.retraction = i.fSharp.hom } := by
  let j := π.retraction
  have : i.toToposHom.pushforward.IsEquivalence := hi.equiv
  let α := Classical.choose π.comp_id
  have hα : X.forgetRing.map (j.comp i).fSharp ≫ α.hom.app (X.forgetRing.obj X.O) =
      𝟙 (X.forgetRing.obj X.O) := Classical.choose_spec π.comp_id
  have hcomp : (i.toToposHom.pushforward ⋙ j.toToposHom.pushforward) ≅ 𝟭 X.Topos := α
  have : (i.toToposHom.pushforward ⋙ j.toToposHom.pushforward).IsEquivalence :=
    Functor.isEquivalence_of_iso hcomp.symm
  have hj : j.toToposHom.pushforward.IsEquivalence :=
    Functor.isEquivalence_of_comp_left i.toToposHom.pushforward j.toToposHom.pushforward
  have : (pushforwardCommRingFunctor i.toToposHom).IsEquivalence :=
    pushforwardCommRingFunctor_isEquivalence i.toToposHom hi.equiv
  have : (pushforwardCommRingFunctor j.toToposHom).IsEquivalence :=
    pushforwardCommRingFunctor_isEquivalence j.toToposHom hj
  have : IsIso (j.comp i).fSharp := by
    have : IsIso (X.forgetRing.map (j.comp i).fSharp) := by
      rw [(α.app (X.forgetRing.obj X.O)).comp_hom_eq_id.mp hα]
      exact (α.app (X.forgetRing.obj X.O)).isIso_inv
    exact isIso_of_reflects_iso _ X.forgetRing
  let β : (pushforwardCommRingFunctor i.toToposHom ⋙
      pushforwardCommRingFunctor j.toToposHom).obj X.O ≅ X.O :=
    pushforwardCommRingCompIso i.toToposHom j.toToposHom X.O ≪≫ (asIso (j.comp i).fSharp).symm
  have hrel : j.fSharp ≫ (pushforwardCommRingFunctor j.toToposHom).map i.fSharp ≫ β.hom =
      𝟙 X.O :=
    (asIso (j.comp i).fSharp).hom_inv_id
  let Gff := Functor.FullyFaithful.ofFullyFaithful (pushforwardCommRingFunctor j.toToposHom)
  let splitSheaf : (pushforwardCommRingFunctor i.toToposHom).obj X.O ⟶ Y.O :=
    Gff.preimage (β.hom ≫ j.fSharp)
  have hsplitmap : (pushforwardCommRingFunctor j.toToposHom).map splitSheaf = β.hom ≫ j.fSharp :=
    Gff.map_preimage _
  have hcancel : j.fSharp ≫ (pushforwardCommRingFunctor j.toToposHom).map i.fSharp = β.inv :=
    β.comp_hom_eq_id.mp hrel
  have hsplitSheaf : splitSheaf ≫ i.fSharp = 𝟙 _ := Gff.map_injective <| by
    rw [CategoryTheory.Functor.map_comp, hsplitmap, Category.assoc, hcancel, β.hom_inv_id]
    exact ((pushforwardCommRingFunctor j.toToposHom).map_id _).symm
  let split := splitSheaf.hom
  let hs : SplitMono split := ⟨i.fSharp.hom, congrArg (fun f ↦ f.hom) hsplitSheaf⟩
  have h_sq : ∀ U : Y.Cᵒᵖ, RingHom.ker (i.fSharp.hom.app U).hom ^ 2 = ⊥ := by
    intro U
    refine le_antisymm ?_ bot_le
    rw [pow_two, Ideal.mul_le]
    intro a ha b hb
    obtain ⟨x, rfl⟩ := (hi.kernel U a).mp (RingHom.mem_ker.mp ha)
    obtain ⟨y, rfl⟩ := (hi.kernel U b).mp (RingHom.mem_ker.mp hb)
    exact hi.square_zero U x y
  exact ⟨split, hs, Deformation.RingThickening.splittingFromTrivialization (A' := Y.O.obj)
    (A := ((pushforwardCommRingFunctor i.toToposHom).obj X.O).obj) split hs h_sq, rfl⟩

end Deformation.ToposThickening
