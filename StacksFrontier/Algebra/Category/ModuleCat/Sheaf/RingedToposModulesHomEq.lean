module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullback
public import StacksFrontier.CategoryTheory.Adjunction.FamilyIndexTransport
public import StacksFrontier.Deformation.ToposThickening.PushforwardComparison.Basic

/-!
# The two readings of a morphism of ringed topoi as the datum of the modules development agree

A morphism of ringed topoi in the sense of Stacks 01D3 part (2) is an
`AlgebraicGeometry.RingedToposHom`: a morphism of the underlying topoi together with the
direct-image form `f♯ : O_D ⟶ f_*O_C` of the structure map, at the level of sheaves of
*commutative* rings. Pullback and pushforward of sheaves of modules are built over a different
structure, `Stacks.Sheaves.RingedToposModules.RingedToposHom`, which works at the level of
sheaves of rings and carries both forms of the structure map together with the equation making
them adjunct. The development reads the first as the second in two ways:

* `AlgebraicGeometry.RingedToposHom.toModulesHom` takes the inverse-image form to be the adjunct
  of `f♯`, read at the level of sheaves of rings, under `f⁻¹ ⊣ f_*` for sheaves of rings;
* `AlgebraicGeometry.RingedToposHom.toRingedToposModulesHom` takes it to be the adjunct of `f♯`
  under the adjunction for sheaves of *commutative* rings, read at the level of sheaves of rings
  afterwards.

This file proves that the two readings are the **same morphism**, so that a result proved for
one applies to the other without a comparison isomorphism. Both pullbacks of sheaves of modules
are then literally the same functor, which is
`AlgebraicGeometry.RingedToposHom.pullbackModules_toRingedToposModulesHom`.

## Main results

* `AlgebraicGeometry.RingedToposHom.toRingedToposModulesHom_eq_toModulesHom`: the two readings
  of a morphism of ringed topoi as the four-field datum of the modules development are equal.
* `AlgebraicGeometry.RingedToposHom.pullbackModules_toRingedToposModulesHom`: consequently the
  pullback of sheaves of modules taken through the first reading is
  `AlgebraicGeometry.RingedToposHom.pullbackModules`.
* `AlgebraicGeometry.RingedToposHom.pushforwardModules_toRingedToposModulesHom`: and the direct
  image taken through the first reading is the direct image taken through the second.
* `Stacks.Sheaves.RingedToposModules.homEquiv_pullbackAdjPushforwardModules_of_eq` and
  `.homEquiv_symm_pullbackAdjPushforwardModules_of_eq`: the Stacks 03D7 adjunction of the modules
  development transposes the same way at two *equal* four-field morphisms of ringed topoi, in
  both directions. These move a whole adjunction across such an equality, which moves the left
  adjoint and the right adjoint at once.
* `.homEquiv_eqToIso_inv_app_comp_pullbackAdjPushforwardModules_of_eq`, in the same namespace:
  the first of those for a morphism out of the pullback at the *source* of the equality, so that
  the transport of the left adjoints appears read backwards on the source.
* `AlgebraicGeometry.RingedToposHom.homEquiv_pullbackAdjPushforwardModules` and
  `.homEquiv_symm_pullbackAdjPushforwardModules`: **the bridge between the two formalizations of
  Stacks 03D7** -- transposing along
  `AlgebraicGeometry.RingedToposHom.pullbackAdjPushforwardModules` is transposing along
  `Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules` at
  `toRingedToposModulesHom`, conjugated by those transports and by the comparison
  `AlgebraicGeometry.RingedToposHom.toModulesPushforwardIso` of the two direct images. Their two
  halves, `.homEquiv_pullbackAdjPushforwardModules_toModulesHom` and
  `.homEquiv_symm_pullbackAdjPushforwardModules_toModulesHom`, are each usable on their own.
* `AlgebraicGeometry.RingedToposHom.unit_app_pullbackAdjPushforwardModules`: the unit of the
  second spelling, through the first.

## Implementation notes

Only the two forms of the structure map have to be compared; the morphism of topoi is the same
in both readings, and the adjunctness field is a proposition.

For the direct-image form that comparison is
`AlgebraicGeometry.RingedToposHom.ringFsharp_eq_structureRingMap`, where the mathematical
content sits: forgetting commutativity carries the adjunction for sheaves of commutative rings
to the one for sheaves of rings. The inverse-image forms then agree because each reading's
direct-image form is the adjunct of its own inverse-image form, so applying the inverse of the
ring-level hom-set bijection to that comparison identifies them.

`AlgebraicGeometry.RingedToposHom.forgetCommRingSheaf_map_fSharpInverseImage` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/PullbackModulesOfIsoStructureMap.lean` is that
same comparison of inverse-image forms, proved there by a longer route through sheaves of sets
which asks the two sites for `CategoryTheory.GrothendieckTopology.HasSheafCompose` of
`CategoryTheory.forget CommRingCat` as well. Those hypotheses are not available here, so the
comparison is taken from the direct-image form instead; the two statements should be merged into
the unconditional one by whoever owns that file.

## References

* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules

universe v u w v' u' w'

namespace AlgebraicGeometry.RingedToposHom

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]

/-- **The two readings of a morphism of ringed topoi as the four-field datum of the modules
development are the same morphism.** The underlying morphism of topoi is the same in both and
the adjunctness field is a proposition, so what has to be compared are the two forms of the
structure map: the direct-image forms agree by
`AlgebraicGeometry.RingedToposHom.ringFsharp_eq_structureRingMap`, and the inverse-image forms
are their adjuncts under `f⁻¹ ⊣ f_*` for sheaves of rings. -/
theorem toRingedToposModulesHom_eq_toModulesHom (f : RingedToposHom X Y) :
    f.toRingedToposModulesHom = f.toModulesHom := by
  have hinv : f.ringFsharpInverseImage = f.fSharpInverseImageRing :=
    ((((ringImageAdjunction f.toToposHom).homEquiv (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).symm_apply_apply
              f.ringFsharpInverseImage).symm).trans
      (congrArg ((ringImageAdjunction f.toToposHom).homEquiv
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).symm f.ringFsharp_eq_structureRingMap)
  have hdir : f.ringFsharp = f.fSharpRing := f.ringFsharp_eq_structureRingMap
  unfold toRingedToposModulesHom toModulesHom
  congr 1

variable [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]

omit [Y.J.HasSheafCompose (forget AddCommGrpCat)] in
/-- The direct image of sheaves of modules taken through
`AlgebraicGeometry.RingedToposHom.toRingedToposModulesHom` is the one taken through
`AlgebraicGeometry.RingedToposHom.toModulesHom`: the two readings of the morphism are equal.

This is the direct-image analogue of
`AlgebraicGeometry.RingedToposHom.pullbackModules_toRingedToposModulesHom`, and it stops where
that one goes on: `AlgebraicGeometry.RingedToposHom.pullbackModules` *is* the pullback of the
second reading by definition, whereas `AlgebraicGeometry.RingedToposHom.pushforwardModules` is a
different construction, agreeing with this one only up to the isomorphism
`AlgebraicGeometry.RingedToposHom.toModulesPushforwardIso`. -/
theorem pushforwardModules_toRingedToposModulesHom (f : RingedToposHom X Y) :
    Stacks.Sheaves.RingedToposModules.pushforwardModules f.toRingedToposModulesHom =
      Stacks.Sheaves.RingedToposModules.pushforwardModules f.toModulesHom :=
  congrArg (fun g ↦ Stacks.Sheaves.RingedToposModules.pushforwardModules g)
    f.toRingedToposModulesHom_eq_toModulesHom

variable [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

omit [X.J.HasSheafCompose (forget AddCommGrpCat)] in
/-- The pullback of sheaves of modules taken through
`AlgebraicGeometry.RingedToposHom.toRingedToposModulesHom` is
`AlgebraicGeometry.RingedToposHom.pullbackModules`: the two readings of the morphism are equal,
and the second pullback is the pullback of the other reading by definition. -/
theorem pullbackModules_toRingedToposModulesHom (f : RingedToposHom X Y) :
    Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules f.toRingedToposModulesHom =
      f.toModulesHom.pullbackModules := by
  rw [f.toRingedToposModulesHom_eq_toModulesHom]

end AlgebraicGeometry.RingedToposHom

namespace Stacks.Sheaves.RingedToposModules

variable {X : AlgebraicGeometry.RingedTopos.{v, u, w}}
  {Y : AlgebraicGeometry.RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  {g g' : RingedToposHom X Y} (h : g = g')
  (G : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
  (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-- **The Stacks 03D7 adjunction transposes the same way at two equal four-field morphisms of
ringed topoi.** This is `CategoryTheory.Adjunction.homEquiv_eqToIso_hom_app_comp_of_eq` for the
family `g ↦ pullbackAdjPushforwardModules g`, with the two categories of sheaves of modules
fixed and the morphism still a variable. Interposing it is what makes the transport usable: the
general statement cannot be instantiated here directly — the unifier is then asked to see
through the definitional unfoldings of the two adjoints at a concrete morphism while the
categories are still metavariables, and exhausts its heartbeats. -/
theorem homEquiv_pullbackAdjPushforwardModules_of_eq
    (u : (g'.pullbackModules).obj G ⟶ F) :
    (pullbackAdjPushforwardModules g').homEquiv G F u =
      (pullbackAdjPushforwardModules g).homEquiv G F
          ((eqToIso (congrArg
              (fun k ↦ Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules k)
              h)).hom.app G ≫ u) ≫
        (eqToIso (congrArg (fun k ↦ pushforwardModules k) h)).hom.app F :=
  ((Iso.eq_comp_inv ((eqToIso (congrArg (fun k ↦ pushforwardModules k) h)).app F)).mp
    (Adjunction.homEquiv_eqToIso_hom_app_comp_of_eq
      (fun k ↦ pullbackAdjPushforwardModules k) h G F u)).symm

/-- **The Stacks 03D7 adjunction transposes back the same way at two equal four-field morphisms
of ringed topoi**, the statement of
`Stacks.Sheaves.RingedToposModules.homEquiv_pullbackAdjPushforwardModules_of_eq` for the inverse
transposition. -/
theorem homEquiv_symm_pullbackAdjPushforwardModules_of_eq
    (v : G ⟶ (pushforwardModules g').obj F) :
    ((pullbackAdjPushforwardModules g').homEquiv G F).symm v =
      (eqToIso (congrArg
          (fun k ↦ Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules k)
          h)).inv.app G ≫
        ((pullbackAdjPushforwardModules g).homEquiv G F).symm
          (v ≫ (eqToIso (congrArg (fun k ↦ pushforwardModules k) h)).inv.app F) :=
  (Iso.eq_inv_comp ((eqToIso (congrArg
      (fun k ↦ Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules k)
      h)).app G)).mpr
    (Adjunction.homEquiv_symm_eqToIso_inv_app_comp_of_eq
      (fun k ↦ pullbackAdjPushforwardModules k) h G F v).symm

/-- **The Stacks 03D7 adjunction transposes the same way at two equal four-field morphisms of
ringed topoi, with the transport applied on the source of the morphism being transposed.** This
is `Stacks.Sheaves.RingedToposModules.homEquiv_pullbackAdjPushforwardModules_of_eq` for a
morphism out of the pullback at `g` rather than at `g'`.

The two differ by cancelling the transport of the left adjoints against itself, and that
cancellation cannot be performed at a use site: there the hom-set bijection and the morphism it
is applied to both have types mentioning the morphism of ringed topoi, and the term the kernel is
then handed does not finish checking. Over the family the cancellation is `subst`, which is
`CategoryTheory.Adjunction.homEquiv_eqToIso_inv_app_comp_of_eq`. -/
theorem homEquiv_eqToIso_inv_app_comp_pullbackAdjPushforwardModules_of_eq
    (k : (g.pullbackModules).obj G ⟶ F) :
    (pullbackAdjPushforwardModules g').homEquiv G F
        ((eqToIso (congrArg
            (fun k ↦ Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules k)
            h)).inv.app G ≫ k) =
      (pullbackAdjPushforwardModules g).homEquiv G F k ≫
        (eqToIso (congrArg (fun k ↦ pushforwardModules k) h)).hom.app F :=
  Adjunction.homEquiv_eqToIso_inv_app_comp_of_eq
    (fun k ↦ pullbackAdjPushforwardModules k) h G F k

end Stacks.Sheaves.RingedToposModules

namespace AlgebraicGeometry.RingedToposHom

/-! ### The two spellings of the Stacks 03D7 adjunction

`Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules f.toRingedToposModulesHom` and
`AlgebraicGeometry.RingedToposHom.pullbackAdjPushforwardModules f` are the two spellings of
Stacks 03D7 for one morphism of ringed topoi, and nothing related them. They differ by two
steps, and the statements below are those two steps and their composites: the equality of the
two readings of the morphism, which moves the left adjoint and the right adjoint at once, and
the comparison `AlgebraicGeometry.RingedToposHom.toModulesPushforwardIso` of the two direct
images, along which the second spelling turns its right adjoint. -/

section Bridge

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (f : RingedToposHom X Y) (G : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
  (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-- Transposing along the Stacks 03D7 adjunction for the two-field morphism of ringed topoi is
transposing along the one of the modules development at
`AlgebraicGeometry.RingedToposHom.toModulesHom` and applying the comparison of the two direct
images afterwards: `CategoryTheory.Adjunction.homEquiv_ofNatIsoRight_apply` at the definition of
the adjunction.

The morphism is handed to the general lemma at the *four-field* spelling of its type. Leaving the
two spellings to the unifier, which has to find the implicit objects through them, exhausts its
heartbeats. -/
theorem homEquiv_pullbackAdjPushforwardModules_toModulesHom
    (u : (f.toModulesHom.pullbackModules).obj G ⟶ F) :
    (pullbackAdjPushforwardModules f).homEquiv G F u =
      (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
          f.toModulesHom).homEquiv G F u ≫ f.toModulesPushforwardIso.hom.app F :=
  Adjunction.homEquiv_ofNatIsoRight_apply
    (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules f.toModulesHom)
    f.toModulesPushforwardIso
    (show (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules f.toModulesHom).obj G ⟶
      F from u)

/-- Transposing back along the Stacks 03D7 adjunction for the two-field morphism of ringed
topoi, through the four-field spelling at
`AlgebraicGeometry.RingedToposHom.toModulesHom`. -/
theorem homEquiv_symm_pullbackAdjPushforwardModules_toModulesHom
    (v : G ⟶ (pushforwardModules f).obj F) :
    ((pullbackAdjPushforwardModules f).homEquiv G F).symm v =
      ((Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
          f.toModulesHom).homEquiv G F).symm (v ≫ f.toModulesPushforwardIso.inv.app F) :=
  Adjunction.homEquiv_ofNatIsoRight_symm_apply
    (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules f.toModulesHom)
    f.toModulesPushforwardIso (show G ⟶ (pushforwardModules f).obj F from v)

/-- The inverse transposition of the modules development crosses the equality of the two
readings of the morphism of ringed topoi. This is
`Stacks.Sheaves.RingedToposModules.homEquiv_symm_pullbackAdjPushforwardModules_of_eq` at the two
readings, stated for a variable morphism out of the direct image: instantiating it at a
composite inside a longer chain exhausts the elaborator, and at a variable it does not. -/
theorem homEquiv_symm_pullbackAdjPushforwardModules_toRingedToposModulesHom
    (v : G ⟶ (Stacks.Sheaves.RingedToposModules.pushforwardModules f.toModulesHom).obj F) :
    ((Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
        f.toModulesHom).homEquiv G F).symm v =
      (eqToIso (congrArg
          (fun k ↦ Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules k)
          f.toRingedToposModulesHom_eq_toModulesHom)).inv.app G ≫
        ((Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
            f.toRingedToposModulesHom).homEquiv G F).symm
          (v ≫ (eqToIso (congrArg
            (fun k ↦ Stacks.Sheaves.RingedToposModules.pushforwardModules k)
            f.toRingedToposModulesHom_eq_toModulesHom)).inv.app F) :=
  Stacks.Sheaves.RingedToposModules.homEquiv_symm_pullbackAdjPushforwardModules_of_eq
    f.toRingedToposModulesHom_eq_toModulesHom G F v

/-- **The two spellings of the Stacks 03D7 adjunction transpose the same way.** Transposing
along `AlgebraicGeometry.RingedToposHom.pullbackAdjPushforwardModules` is transposing along
`Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules` at
`AlgebraicGeometry.RingedToposHom.toRingedToposModulesHom`, with the transport of the left
adjoints applied to the morphism first and, after it, the transport of the right adjoints
followed by the comparison `AlgebraicGeometry.RingedToposHom.toModulesPushforwardIso` of the two
direct images.

This is the bridge between the two formalizations of Stacks 03D7: it carries a transposition
computed over either spelling to the other. -/
theorem homEquiv_pullbackAdjPushforwardModules (u : (f.toModulesHom.pullbackModules).obj G ⟶ F) :
    (pullbackAdjPushforwardModules f).homEquiv G F u =
      (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
            f.toRingedToposModulesHom).homEquiv G F
          ((eqToIso (congrArg
              (fun k ↦ Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules k)
              f.toRingedToposModulesHom_eq_toModulesHom)).hom.app G ≫ u) ≫
        (eqToIso (congrArg
            (fun k ↦ Stacks.Sheaves.RingedToposModules.pushforwardModules k)
            f.toRingedToposModulesHom_eq_toModulesHom)).hom.app F ≫
          f.toModulesPushforwardIso.hom.app F :=
  (homEquiv_pullbackAdjPushforwardModules_toModulesHom f G F u).trans
    ((congrArg (fun z ↦ z ≫ f.toModulesPushforwardIso.hom.app F)
      (Stacks.Sheaves.RingedToposModules.homEquiv_pullbackAdjPushforwardModules_of_eq
        f.toRingedToposModulesHom_eq_toModulesHom G F
        (show (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
          f.toModulesHom).obj G ⟶ F from u))).trans
      (Category.assoc
        ((Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
              f.toRingedToposModulesHom).homEquiv G F
            ((eqToIso (congrArg
                (fun k ↦ Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules k)
                f.toRingedToposModulesHom_eq_toModulesHom)).hom.app G ≫ u))
        ((eqToIso (congrArg
            (fun k ↦ Stacks.Sheaves.RingedToposModules.pushforwardModules k)
            f.toRingedToposModulesHom_eq_toModulesHom)).hom.app F)
        (f.toModulesPushforwardIso.hom.app F)))

/-- **The two spellings of the Stacks 03D7 adjunction transpose back the same way**, the
statement of `AlgebraicGeometry.RingedToposHom.homEquiv_pullbackAdjPushforwardModules` for the
inverse transposition. -/
theorem homEquiv_symm_pullbackAdjPushforwardModules
    (v : G ⟶ (pushforwardModules f).obj F) :
    ((pullbackAdjPushforwardModules f).homEquiv G F).symm v =
      (eqToIso (congrArg
          (fun k ↦ Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules k)
          f.toRingedToposModulesHom_eq_toModulesHom)).inv.app G ≫
        ((Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
            f.toRingedToposModulesHom).homEquiv G F).symm
          ((v ≫ f.toModulesPushforwardIso.inv.app F) ≫
            (eqToIso (congrArg
              (fun k ↦ Stacks.Sheaves.RingedToposModules.pushforwardModules k)
              f.toRingedToposModulesHom_eq_toModulesHom)).inv.app F) :=
  (homEquiv_symm_pullbackAdjPushforwardModules_toModulesHom f G F v).trans
    (homEquiv_symm_pullbackAdjPushforwardModules_toRingedToposModulesHom f G F
      (v ≫ f.toModulesPushforwardIso.inv.app F))

/-- The unit of the Stacks 03D7 adjunction for the two-field morphism of ringed topoi, as a
transposition of the identity read through the four-field spelling. -/
private theorem unit_app_pullbackAdjPushforwardModules_homEquiv_id :
    (pullbackAdjPushforwardModules f).unit.app G =
      (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
            f.toRingedToposModulesHom).homEquiv G
          ((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules f.toModulesHom).obj G)
          ((eqToIso (congrArg
                (fun k ↦ Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules k)
                f.toRingedToposModulesHom_eq_toModulesHom)).hom.app G ≫
            CategoryStruct.id
              ((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
                  f.toModulesHom).obj G)) ≫
        (eqToIso (congrArg
            (fun k ↦ Stacks.Sheaves.RingedToposModules.pushforwardModules k)
            f.toRingedToposModulesHom_eq_toModulesHom)).hom.app
            ((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
                f.toModulesHom).obj G) ≫
          f.toModulesPushforwardIso.hom.app
            ((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
                f.toModulesHom).obj G) :=
  (Adjunction.homEquiv_id (pullbackAdjPushforwardModules f) G).symm.trans
    (homEquiv_pullbackAdjPushforwardModules f G
      ((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules f.toModulesHom).obj G)
      (CategoryStruct.id _))

/-- That transposition of the identity, computed: the identity drops out and what is left is the
unit of the four-field adjunction followed by its direct image of the transport. -/
private theorem homEquiv_eqToIso_hom_app_comp_id :
    (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
          f.toRingedToposModulesHom).homEquiv G
        ((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules f.toModulesHom).obj G)
        ((eqToIso (congrArg
              (fun k ↦ Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules k)
              f.toRingedToposModulesHom_eq_toModulesHom)).hom.app G ≫
          CategoryStruct.id
            ((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
                f.toModulesHom).obj G)) =
      (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
          f.toRingedToposModulesHom).unit.app G ≫
        (Stacks.Sheaves.RingedToposModules.pushforwardModules
            f.toRingedToposModulesHom).map
          ((eqToIso (congrArg
            (fun k ↦ Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules k)
            f.toRingedToposModulesHom_eq_toModulesHom)).hom.app G) :=
  (congrArg
      ((Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
          f.toRingedToposModulesHom).homEquiv G
        ((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules f.toModulesHom).obj G))
      (Category.comp_id ((eqToIso (congrArg
        (fun k ↦ Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules k)
        f.toRingedToposModulesHom_eq_toModulesHom)).hom.app G))).trans
    (Adjunction.homEquiv_unit
      (adj := Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
        f.toRingedToposModulesHom)
      (f := (eqToIso (congrArg
        (fun k ↦ Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules k)
        f.toRingedToposModulesHom_eq_toModulesHom)).hom.app G))

/-- **The unit of the Stacks 03D7 adjunction for the two-field morphism of ringed topoi, through
the four-field spelling.** It is the unit of the modules development's adjunction at
`AlgebraicGeometry.RingedToposHom.toRingedToposModulesHom`, followed by the direct image of the
transport of the left adjoints and then by the transport of the right adjoints and the
comparison of the two direct images. -/
theorem unit_app_pullbackAdjPushforwardModules :
    (pullbackAdjPushforwardModules f).unit.app G =
      (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
          f.toRingedToposModulesHom).unit.app G ≫
        (Stacks.Sheaves.RingedToposModules.pushforwardModules
            f.toRingedToposModulesHom).map
          ((eqToIso (congrArg
            (fun k ↦ Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules k)
            f.toRingedToposModulesHom_eq_toModulesHom)).hom.app G) ≫
        (eqToIso (congrArg
            (fun k ↦ Stacks.Sheaves.RingedToposModules.pushforwardModules k)
            f.toRingedToposModulesHom_eq_toModulesHom)).hom.app
            ((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
                f.toModulesHom).obj G) ≫
          f.toModulesPushforwardIso.hom.app
            ((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
                f.toModulesHom).obj G) :=
  (unit_app_pullbackAdjPushforwardModules_homEquiv_id f G).trans
    ((congrArg
        (fun z ↦ z ≫ (eqToIso (congrArg
              (fun k ↦ Stacks.Sheaves.RingedToposModules.pushforwardModules k)
              f.toRingedToposModulesHom_eq_toModulesHom)).hom.app
              ((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
                  f.toModulesHom).obj G) ≫
            f.toModulesPushforwardIso.hom.app
              ((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
                  f.toModulesHom).obj G))
        (homEquiv_eqToIso_hom_app_comp_id f G)).trans
      (Category.assoc
        ((Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
          f.toRingedToposModulesHom).unit.app G)
        ((Stacks.Sheaves.RingedToposModules.pushforwardModules
            f.toRingedToposModulesHom).map
          ((eqToIso (congrArg
            (fun k ↦ Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules k)
            f.toRingedToposModulesHom_eq_toModulesHom)).hom.app G))
        ((eqToIso (congrArg
              (fun k ↦ Stacks.Sheaves.RingedToposModules.pushforwardModules k)
              f.toRingedToposModulesHom_eq_toModulesHom)).hom.app
              ((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
                  f.toModulesHom).obj G) ≫
            f.toModulesPushforwardIso.hom.app
              ((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
                  f.toModulesHom).obj G))))

end Bridge

end AlgebraicGeometry.RingedToposHom

end
