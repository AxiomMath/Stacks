module

public import StacksFrontier.Deformation.ToposThickening.ModulesOnThickening.ClosedImmersion
public import StacksFrontier.Deformation.ToposThickening.Trivialization.AdjunctionForget

/-!
# The abelian structure on modules over the target of a thickening

Sheaves of modules over the structure sheaf of the *target* of a first order thickening of ringed
topoi form an abelian category. This does not follow from
`AlgebraicGeometry.SheafOfModules.instAbelianSheafOfModules`: that instance needs
`HasWeakSheafify J AddCommGrpCat` and `J.WEqualsLocallyBijective AddCommGrpCat` on the site, and a
thickening carries those hypotheses on the *source* site only. It is obtained instead by transport
along the equivalence `Mod(i⁻¹O) ≃ Mod(O)` given by the direct image on modules of the auxiliary
morphism `Deformation.ToposThickening.inverseImageHom`, whose source is a category of modules on
the source site.

## Main definitions

* `Deformation.ToposThickening.inverseImageRingedTopos` and
  `Deformation.ToposThickening.inverseImageHom`: the auxiliary ringed topos `(Sh(C), i⁻¹O)` and
  the morphism out of it whose structure map is the unit of the commutative-ring image
  adjunction.
* `Deformation.ToposThickening.FirstOrderThickening.inverseImageClosedRingedImmersion`: that
  morphism read as a closed immersion; its ideal is zero.
* `Deformation.ToposThickening.FirstOrderThickening.abelian`: the abelian structure.

## Main results

* `Deformation.ToposThickening.isEquivalence_pushforwardModules_of_isIso_fSharp`: the direct image
  on modules along a closed immersion of ringed topoi whose structure map is invertible on
  underlying sheaves of sets is an equivalence.

## Implementation notes

The equivalence is `Stacks 08M3` twice over: full faithfulness is
`AlgebraicGeometry.ClosedRingedImmersion.pushforwardModules_fullyFaithful`, and essential
surjectivity is
`AlgebraicGeometry.ClosedRingedImmersion.pushforwardModules_essImage_iff_ideal_annihilates`
applied to an immersion whose ideal is zero, which it is because the structure map is injective on
sections.

## References

* [Stacks Project, Tag 08MP](https://stacks.math.columbia.edu/tag/08MP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom ClosedRingedImmersion)
open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor commRingImageAdjunction
  commRingImageAdjunction_unit_forget)

universe v u v' u' w

namespace Deformation.ToposThickening

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The auxiliary ringed topos used to transport the abelian structure: the source site carrying
the inverse image of the structure sheaf of the target. -/
noncomputable abbrev inverseImageRingedTopos (i : RingedToposHom X Y) : RingedTopos.{v, u, w} :=
  { C := X.C, J := X.J,
    O := ((inverseImageCommRingFunctor i.toToposHom).obj Y.O : Sheaf X.J CommRingCat.{w}) }

/-- The auxiliary morphism of ringed topoi from `inverseImageRingedTopos` to the target, whose
structure map is the unit of the commutative-ring image adjunction. -/
noncomputable def inverseImageHom (i : RingedToposHom X Y) :
    RingedToposHom (inverseImageRingedTopos i) Y where
  toToposHom := i.toToposHom
  fSharp := (commRingImageAdjunction i.toToposHom).unit.app Y.O

omit [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The structure map of the auxiliary morphism is invertible on underlying sheaves of sets: it
is the unit of `i⁻¹ ⊣ i_*`, and the direct image of sheaves of sets is an equivalence. -/
lemma FirstOrderThickening.isIso_forgetRing_inverseImageHom_fSharp {i : RingedToposHom X Y}
    (hi : FirstOrderThickening i) : IsIso (Y.forgetRing.map (inverseImageHom i).fSharp) := by
  have heq : i.toToposHom.pushforward.IsEquivalence := hi.equiv
  change IsIso ((sheafCompose Y.J (forget CommRingCat.{w})).map
    ((commRingImageAdjunction i.toToposHom).unit.app Y.O))
  rw [commRingImageAdjunction_unit_forget]
  have hu : IsIso i.toToposHom.adj.unit := by
    have := fun Z => Adjunction.isIso_unit_app_of_iso i.toToposHom.adj
      (i.toToposHom.pushforward.objObjPreimageIso Z).symm
    exact NatIso.isIso_of_isIso_app _
  exact NatIso.isIso_app_of_isIso _ _

/-- The auxiliary morphism, read as a closed immersion of ringed topoi. Its ideal is zero, since
its structure map is an isomorphism. -/
noncomputable def FirstOrderThickening.inverseImageClosedRingedImmersion
    {i : RingedToposHom X Y} (hi : FirstOrderThickening i) :
    ClosedRingedImmersion.{v, u, v', u', w} where
  source := inverseImageRingedTopos i
  target := Y
  hom := inverseImageHom i
  isClosedImmersion := hi.isClosedImmersion
  structureMap_surjective :=
    have := hi.isIso_forgetRing_inverseImageHom_fSharp
    inferInstance

/-- **The direct image on modules along a closed immersion with invertible structure map is an
equivalence.** The ideal of such an immersion is zero, so every module over the target structure
sheaf satisfies the annihilation criterion of Stacks 08M3 and is therefore a direct image; the
direct image is fully faithful by Stacks 08M3 as well. -/
lemma isEquivalence_pushforwardModules_of_isIso_fSharp
    (S : AlgebraicGeometry.ClosedRingedImmersion.{v, u, v', u', w})
    [HasWeakSheafify S.source.J AddCommGrpCat.{w}]
    [S.source.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (h : IsIso (S.target.forgetRing.map S.hom.fSharp)) :
    S.hom.pushforwardModules.IsEquivalence := by
  have ff := (ClosedRingedImmersion.pushforwardModules_fullyFaithful S).some
  have : S.hom.pushforwardModules.Full := ff.full
  have : S.hom.pushforwardModules.Faithful := ff.faithful
  have : S.hom.pushforwardModules.EssSurj := ⟨fun M => by
    refine (ClosedRingedImmersion.pushforwardModules_essImage_iff_ideal_annihilates S M).2 ?_
    intro U a ha m
    rw [S.ideal_obj] at ha
    have hzero : S.hom.fSharp.hom.app U a = S.hom.fSharp.hom.app U 0 := by
      change (S.hom.fSharp.hom.app U).hom a = 0 at ha
      simpa only [map_zero] using ha
    have hiso : IsIso ((S.target.forgetRing.map S.hom.fSharp).hom.app U) :=
      have := h
      inferInstance
    have hbij : Function.Injective ((S.target.forgetRing.map S.hom.fSharp).hom.app U) :=
      ((isIso_iff_bijective _).1 hiso).1
    have ha0 : a = 0 := hbij hzero
    rw [ha0, zero_smul]⟩
  exact { }

/-- **Sheaves of modules on the target of a first order thickening form an abelian category.**

The hypotheses of a thickening put no sheafification condition on the target site, so this does
not follow from `AlgebraicGeometry.SheafOfModules.instAbelianSheafOfModules`; it is transported
along the equivalence given by the direct image on modules of the auxiliary morphism, whose
source is a category of modules on the source site, where sheafification is available. -/
@[instance_reducible]
noncomputable def FirstOrderThickening.abelian {i : RingedToposHom X Y}
    (hi : FirstOrderThickening i) :
    Abelian (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) := by
  let S := hi.inverseImageClosedRingedImmersion
  letI : HasWeakSheafify S.source.J AddCommGrpCat.{w} :=
    inferInstanceAs (HasWeakSheafify X.J AddCommGrpCat.{w})
  letI : S.source.J.WEqualsLocallyBijective AddCommGrpCat.{w} :=
    inferInstanceAs (X.J.WEqualsLocallyBijective AddCommGrpCat.{w})
  haveI := isEquivalence_pushforwardModules_of_isIso_fSharp S
    hi.isIso_forgetRing_inverseImageHom_fSharp
  exact @abelianOfEquivalence _ _ _ _ _ _ _ _
    S.hom.pushforwardModules.asEquivalence.symm.isEquivalence_functor

end Deformation.ToposThickening

end
