module

public import StacksFrontier.Deformation.ToposThickening.Basic
public import StacksFrontier.Deformation.ToposThickening.Trivialization.AdjunctionForget
public import StacksFrontier.Deformation.ToposThickening.Trivialization.Basic

/-!
# A splitting of a thickening with an equivalence of topoi determines a trivialization

`Deformation.ToposThickening.trivializationOfSplitting` (Stacks 08MG) turns a section of the
inverse-image form of the structure map of a first order thickening into a trivialization whose
structure map is that section. Its proof uses nothing of the first order thickening but the
equivalence of underlying topoi. This file states the construction at that generality, for a
morphism of ringed topoi whose direct image is an equivalence, so that it applies to a
thickening presented by the predicate `Deformation.ToposThickening.IsFirstOrderThickening`,
which names no ideal over the base, as the three-site sequences of Stacks 08ML are.

## Main definitions

* `Deformation.ToposThickening.trivializationOfSplittingOfEquivalence`: the trivialization
  attached to a section, for a morphism whose direct image is an equivalence.

## References

* [Stacks Project, Tag 08MG](https://stacks.math.columbia.edu/tag/08MG)
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor pushforwardCommRingFunctor)

universe v u w v' u' w'

namespace Deformation.ToposThickening

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]

/-- A section of the inverse-image form of the structure map of a morphism of ringed topoi whose
direct image is an equivalence determines a trivialization whose structure map is the given
section. -/
noncomputable def trivializationOfSplittingOfEquivalence (i : RingedToposHom X Y)
    (hi : i.toToposHom.pushforward.IsEquivalence)
    (split : X.O ⟶ (inverseImageCommRingFunctor i.toToposHom).obj Y.O)
    (split_comp : split ≫ i.fSharpInverseImage = 𝟙 X.O) :
    { π : Trivialization i //
      ∃ α : pushforwardCommRingFunctor π.retraction.toToposHom ≅
          inverseImageCommRingFunctor i.toToposHom,
        π.retraction.fSharp ≫ α.hom.app Y.O = split } := by
  have : i.toToposHom.pushforward.IsEquivalence := hi
  let e₀ := i.toToposHom.pushforward.asEquivalence
  let hInv : e₀.inverse ≅ i.toToposHom.inverseImage :=
    Adjunction.leftAdjointUniq e₀.symm.toAdjunction i.toToposHom.adj
  let e := e₀.changeInverse hInv
  let r : RingedToposHom Y X :=
    { toToposHom :=
        { pushforward := i.toToposHom.inverseImage
          inverseImage := i.toToposHom.pushforward
          adj := e.toAdjunction
          preservesFiniteLimits := by infer_instance }
      fSharp := split }
  refine ⟨⟨r, ?_⟩, ?_⟩
  · refine ⟨e.unitIso.symm, ?_⟩
    rw [RingedToposHom.comp_fSharp_forget]
    change X.forgetRing.map split ≫
        i.toToposHom.inverseImage.map (Y.forgetRing.map i.fSharp) ≫
          e.unitIso.inv.app (X.forgetRing.obj X.O) = 𝟙 _
    have hc : e.unitIso.inv.app (X.forgetRing.obj X.O) =
        i.toToposHom.adj.counit.app (X.forgetRing.obj X.O) := by
      change hInv.inv.app (i.toToposHom.pushforward.obj (X.forgetRing.obj X.O)) ≫
          e₀.unitIso.inv.app (X.forgetRing.obj X.O) = _
      have huniq :
          hInv.hom.app (i.toToposHom.pushforward.obj (X.forgetRing.obj X.O)) ≫
              i.toToposHom.adj.counit.app (X.forgetRing.obj X.O) =
            e₀.unitIso.inv.app (X.forgetRing.obj X.O) :=
        Adjunction.leftAdjointUniq_hom_app_counit
          e₀.symm.toAdjunction i.toToposHom.adj (X.forgetRing.obj X.O)
      rw [← huniq, Iso.inv_hom_id_app_assoc]
    rw [hc]
    exact (congrArg (fun m ↦ X.forgetRing.map split ≫ m)
        (RingedToposHom.fSharpInverseImage_forget i).symm).trans
      ((X.forgetRing.map_comp split i.fSharpInverseImage).symm.trans
        ((congrArg X.forgetRing.map split_comp).trans (X.forgetRing.map_id X.O)))
  · exact ⟨Iso.refl _, rfl⟩

end Deformation.ToposThickening

end
