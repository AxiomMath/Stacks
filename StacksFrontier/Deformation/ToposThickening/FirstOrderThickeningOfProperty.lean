module

public import StacksFrontier.Deformation.ToposThickening.MorphismOfThickeningsFirstOrder
public import StacksFrontier.Deformation.ToposThickening.RestrictScalarsEssentialImage

/-!
# A first order thickening of ringed topoi, from the property

Stacks 08M7 calls a morphism of ringed topoi `i : (Sh(C), O) ⟶ (Sh(D), O')` a *first order
thickening* when it is a thickening (its underlying morphism of topoi is an equivalence and
`O' ⟶ i_*O` is surjective with locally nilpotent kernel) whose kernel ideal has square zero; this
is the property `Deformation.ToposThickening.IsFirstOrderThickening`. Stacks 08MB works with the
datum `Deformation.ToposThickening.FirstOrderThickening`, which in addition names the square-zero
ideal as a module over the quotient `i_*O`. This file constructs the datum from the property: the
ideal is the kernel ideal of the structure map, which its square-zero property makes a module
over `i_*O`.

## Main definitions

* `Deformation.ToposThickening.FirstOrderThickening.ofIsFirstOrderThickening`: the datum of
  Stacks 08MB attached to a first order thickening in the sense of Stacks 08M7.

## References

* [Stacks Project, Tag 08M7](https://stacks.math.columbia.edu/tag/08M7)
* [Stacks Project, Tag 08MB](https://stacks.math.columbia.edu/tag/08MB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom ClosedRingedImmersion)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor)

universe v u w v' u'

namespace Deformation.ToposThickening

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  {i : RingedToposHom X Y}

/-- **Stacks 08MB from Stacks 08M7.** A first order thickening of ringed topoi, in the sense of
the property `Deformation.ToposThickening.IsFirstOrderThickening`, with its square-zero ideal
named: the kernel ideal of the structure map, read as a module over `i_*O` through the
essential-image criterion of restriction of scalars (the ideal is annihilated by itself). -/
noncomputable def FirstOrderThickening.ofIsFirstOrderThickening (hi : IsFirstOrderThickening i) :
    FirstOrderThickening i :=
  haveI : Presheaf.IsLocallySurjective Y.J
      ((sheafCompose Y.J (forget₂ CommRingCat.{w} RingCat.{w})).map i.fSharp).hom := by
    have h : Presheaf.IsLocallySurjective Y.J i.fSharp.hom := hi.1.2.1
    exact ⟨fun {_} s => h.imageSieve_mem s⟩
  have hE := essImage_restrictScalars_of_smul_eq_zero
    ((sheafCompose Y.J (forget₂ CommRingCat.{w} RingCat.{w})).map i.fSharp)
    hi.isThickening.closedRingedImmersion.ideal.toSheafOfModules (fun U a ha m => by
      apply Subtype.ext
      have hm : m.1 ∈ RingHom.ker ((i.fSharp.hom.app U).hom) :=
        (ClosedRingedImmersion.ideal_obj hi.isThickening.closedRingedImmersion U) ▸ m.2
      exact hi.2 U a m.1 ha hm)
  { equiv := hi.1.1
    surjective := hi.1.2.1
    I := hE.witness
    incl := hE.getIso.hom ≫ hi.isThickening.closedRingedImmersion.ideal.ι
    kernel := fun U a => ⟨fun ha => ⟨hE.getIso.inv.val.app U ⟨a, ha⟩,
        congrArg Subtype.val (congrArg (fun φ => φ.val.app U ⟨a, ha⟩) hE.getIso.inv_hom_id)⟩,
      by rintro ⟨b, rfl⟩; exact (hE.getIso.hom.val.app U b).2⟩
    injective := fun U b b' hbb' => by
      have h1 : hE.getIso.hom.val.app U b = hE.getIso.hom.val.app U b' := Subtype.ext hbb'
      exact ((congrArg (fun φ => φ.val.app U b) hE.getIso.hom_inv_id).symm.trans
        (congrArg (hE.getIso.inv.val.app U) h1)).trans
        (congrArg (fun φ => φ.val.app U b') hE.getIso.hom_inv_id)
    square_zero := fun U a b =>
      hi.2 U _ _ (hE.getIso.hom.val.app U a).2 (hE.getIso.hom.val.app U b).2 }

end Deformation.ToposThickening

end
