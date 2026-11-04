module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.KernelIdealSheaf
public import StacksFrontier.Deformation.ToposThickening.Basic
public import StacksFrontier.Deformation.ToposThickening.RestrictScalarsEssentialImage

/-!
# A first order thickening from a square-zero kernel

`Deformation.ToposThickening.FirstOrderThickening` (Stacks 08MB) records, besides the three
conditions on a morphism `i : (Sh(C), O) ⟶ (Sh(D), O')` of ringed topoi — the geometric morphism
is an equivalence, `i^♯ : O' ⟶ i_*O` is locally surjective, and its kernel has square zero — the
kernel `I` itself, as an `i_*O`-module with an inclusion into `O'`. This file shows that the three
conditions suffice: the kernel ideal sheaf of `i^♯` is annihilated by itself, so it descends along
the locally surjective `i^♯` to an `i_*O`-module (Stacks 08M3, the essential-image criterion for
restriction of scalars).

## Main definitions

* `Deformation.ToposThickening.FirstOrderThickening.ofSquareZeroKernel`: the first order
  thickening attached to a morphism of ringed topoi satisfying the three conditions.

## References

* [Stacks Project, Tag 08MB](https://stacks.math.columbia.edu/tag/08MB)
* [Stacks Project, Tag 08M3](https://stacks.math.columbia.edu/tag/08M3)
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor)

universe v u w v' u' w'

namespace Deformation.ToposThickening

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]

/-- The structure map of `i` as a morphism of the underlying sheaves of rings. -/
noncomputable abbrev fSharpRingSheafMap (i : RingedToposHom X Y) :
    Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
      Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O) :=
  (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp

/-- **A morphism of ringed topoi whose geometric morphism is an equivalence, whose structure map
is locally surjective and whose structure map has square-zero kernel is a first order thickening.**
The square-zero ideal is the kernel ideal sheaf of `i^♯`, descended to an `i_*O`-module along
`i^♯`: it is annihilated by itself, which is the essential-image criterion for restriction of
scalars along a locally surjective map. -/
noncomputable def FirstOrderThickening.ofSquareZeroKernel (i : RingedToposHom X Y)
    (hequiv : i.toToposHom.pushforward.IsEquivalence)
    (hsurj : Presheaf.IsLocallySurjective Y.J i.fSharp.hom)
    (hsq : ∀ (U : Y.Cᵒᵖ) (a b : Y.O.obj.obj U), i.fSharp.hom.app U a = 0 →
      i.fSharp.hom.app U b = 0 → a * b = 0) :
    FirstOrderThickening i :=
  have : Presheaf.IsLocallySurjective Y.J (fSharpRingSheafMap i).hom :=
    ⟨fun {_} x => hsurj.imageSieve_mem x⟩
  have hM : (SheafOfModules.restrictScalars.{w'} (fSharpRingSheafMap i)).essImage
      (SheafOfModules.kerIdeal (fSharpRingSheafMap i)).toSheafOfModules :=
    essImage_restrictScalars_of_smul_eq_zero (fSharpRingSheafMap i) _ fun U a ha m =>
      Subtype.ext (hsq U a m.1 ha ((SheafOfModules.mem_kerIdeal _ U m.1).1 m.2))
  { equiv := hequiv
    surjective := hsurj
    I := hM.witness
    incl := hM.getIso.hom ≫ (SheafOfModules.kerIdeal (fSharpRingSheafMap i)).ι
    kernel := fun U a => by
      constructor
      · intro ha
        let a' : ToType ((SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).val.obj
          U) := a
        have ha' : a' ∈ (SheafOfModules.kerIdeal (fSharpRingSheafMap i)).obj U :=
          (SheafOfModules.mem_kerIdeal (fSharpRingSheafMap i) U a).2 ha
        refine ⟨hM.getIso.inv.val.app U ⟨a', ha'⟩, ?_⟩
        have e2 : hM.getIso.hom.val.app U (hM.getIso.inv.val.app U ⟨a', ha'⟩) = ⟨a', ha'⟩ :=
          congrArg (fun φ => φ.val.app U ⟨a', ha'⟩) hM.getIso.inv_hom_id
        change (SheafOfModules.kerIdeal (fSharpRingSheafMap i)).ι.val.app U
          (hM.getIso.hom.val.app U (hM.getIso.inv.val.app U ⟨a', ha'⟩)) = a
        exact congrArg ((SheafOfModules.kerIdeal (fSharpRingSheafMap i)).ι.val.app U) e2
      · rintro ⟨b, rfl⟩
        exact (SheafOfModules.mem_kerIdeal _ U _).1 (hM.getIso.hom.val.app U b).2
    injective := fun U b b' h => by
      have h' : hM.getIso.hom.val.app U b = hM.getIso.hom.val.app U b' := Subtype.ext h
      have e : ∀ c, hM.getIso.inv.val.app U (hM.getIso.hom.val.app U c) = c := fun c =>
        congrArg (fun φ => φ.val.app U c) hM.getIso.hom_inv_id
      simpa only [e] using congrArg (hM.getIso.inv.val.app U) h'
    square_zero := fun U b b' =>
      hsq U _ _ ((SheafOfModules.mem_kerIdeal _ U _).1 (hM.getIso.hom.val.app U b).2)
        ((SheafOfModules.mem_kerIdeal _ U _).1 (hM.getIso.hom.val.app U b').2) }

end Deformation.ToposThickening

end
