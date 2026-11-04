module

public import StacksFrontier.Deformation.ToposThickening.Basic
public import StacksFrontier.Deformation.ToposThickening.Trivialization.AdjunctionForget
public import StacksFrontier.Deformation.ToposThickening.Trivialization.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# A splitting determines a trivialization of a first order thickening

A splitting of the structure-sheaf quotient of a first order thickening of ringed topoi
determines a retraction of the thickening.

## Main results

* `Deformation.ToposThickening.trivializationOfSplitting` constructs a trivialization from a
  section of the structure-sheaf map and identifies its structure map with that section.

## Implementation notes

The splitting is stated on the source topos as a section of the inverse-image form of `i♯`. The
structure map of the resulting retraction is identified with this section through an isomorphism
between the retraction's direct image and the inverse image of the thickening. The square-zero
ideal and its direct sum decomposition are carried by the first order thickening; the proof of
this construction only uses the section of the quotient map, which is why the thickening itself
appears as an unused hypothesis.

The retraction is built from the equivalence of underlying topoi: its direct image is the
inverse image `i⁻¹` of the thickening, and its adjunction is the one obtained by replacing the
inverse of the equivalence `i_*` by `i⁻¹`, the two being identified by uniqueness of left
adjoints. With that replacement the unit of the equivalence is the counit of `i⁻¹ ⊣ i_*`, which
is exactly what turns the identity `split ≫ i♯ = 𝟙` into the compatibility required of a
trivialization.

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

/-- A splitting of the structure sheaf of a first order thickening determines a trivialization
whose structure map is the given section. -/
@[stacks 08MG "splitting_determines_trivialization"]
noncomputable def trivializationOfSplitting (i : RingedToposHom X Y)
    (_hi : FirstOrderThickening i)
    (split : X.O ⟶ (inverseImageCommRingFunctor i.toToposHom).obj Y.O)
    (split_comp : split ≫ i.fSharpInverseImage = 𝟙 X.O) :
    { π : Trivialization i //
      ∃ α : pushforwardCommRingFunctor π.retraction.toToposHom ≅
          inverseImageCommRingFunctor i.toToposHom,
        π.retraction.fSharp ≫ α.hom.app Y.O = split } := by
  have : i.toToposHom.pushforward.IsEquivalence := _hi.equiv
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
      calc
        _ = hInv.inv.app (i.toToposHom.pushforward.obj (X.forgetRing.obj X.O)) ≫
            (hInv.hom.app (i.toToposHom.pushforward.obj (X.forgetRing.obj X.O)) ≫
              i.toToposHom.adj.counit.app (X.forgetRing.obj X.O)) := by rw [huniq]
        _ = _ := by
          rw [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
    rw [hc]
    exact (congrArg (fun m ↦ X.forgetRing.map split ≫ m)
        (RingedToposHom.fSharpInverseImage_forget i).symm).trans
      ((X.forgetRing.map_comp split i.fSharpInverseImage).symm.trans
        ((congrArg X.forgetRing.map split_comp).trans (X.forgetRing.map_id X.O)))
  · exact ⟨Iso.refl _, rfl⟩

end Deformation.ToposThickening
