module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedSmallEtaleRingedToposConjugate

/-!
# Conjugating a composite of morphisms of the small étale ringed topoi of representable spaces

`AlgebraicGeometry.Space.schemeOfRepresentedRingedToposHom` reads a morphism of the small étale
ringed topoi of two representable algebraic spaces over a big fppf site as a morphism of the
small étale ringed topoi of the two underlying schemes, by conjugating with the identification
of the two readings of a chart.  This file records that the conjugation is compatible with
composition: the conjugate of a composite is 2-isomorphic to the composite of the conjugates.

The two differ by the identification of the middle chart taken in both directions, and
`AlgebraicGeometry.Space.representedSmallEtaleRingedToposInverseComp` says that composite is
2-isomorphic to the identity.  So the content is a chain of
`AlgebraicGeometry.RingedToposHom.TwoIso.associator`, `.whiskerLeft`, `.whiskerRight` and the
unitor `.idComp`, and nothing else.

This is what lets a 2-isomorphism between a composite of morphisms of the small étale ringed
topoi of charts and a structure morphism be carried to the scheme level, where
[Stacks Project, Tag 04LW] turns it into an equality of morphisms of schemes.  That equality is
what exhibits the morphism of schemes produced by [Stacks Project, Tag 04I6] as a morphism over
the base.

## Main definitions

* `AlgebraicGeometry.RingedToposHom.TwoIso.compConjugate`: the generic computation in the
  2-category of ringed topoi, with the six ringed topoi and the six morphisms as variables.

## Main results

* `AlgebraicGeometry.Space.schemeOfRepresentedRingedToposHomComp`: the conjugate of a composite
  is 2-isomorphic to the composite of the conjugates.

## Implementation notes

The generic computation is separated out because instantiating the chain directly at
`AlgebraicGeometry.Space.schemeOfRepresentedRingedToposHom` exhausts the heartbeat budget at
`isDefEq`: each step of the chain has to re-solve the shape of the conjugate against a
metavariable.  With the computation done once at plain variables, the instantiation is a single
unification, and the six morphisms are passed explicitly so that even that one is directed.

## References

* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
* [Stacks Project, Tag 04IG](https://stacks.math.columbia.edu/tag/04IG)
* [Stacks Project, Tag 04KL](https://stacks.math.columbia.edu/tag/04KL)
* [Stacks Project, Tag 04LW](https://stacks.math.columbia.edu/tag/04LW)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.RingedToposHom

section CompConjugation

universe vP uP wP vQ uQ wQ vR uR wR vR' uR' wR' vT uT wT vT' uT' wT'

variable {P : RingedTopos.{vP, uP, wP}} {Q : RingedTopos.{vQ, uQ, wQ}}
  {R : RingedTopos.{vR, uR, wR}} {R' : RingedTopos.{vR', uR', wR'}}
  {T : RingedTopos.{vT, uT, wT}} {T' : RingedTopos.{vT', uT', wT'}}
  [P.J.HasSheafCompose (forget RingCat.{wP})]
  [Q.J.HasSheafCompose (forget RingCat.{wQ})]
  [R.J.HasSheafCompose (forget RingCat.{wR})]
  [R'.J.HasSheafCompose (forget RingCat.{wR'})]
  [T.J.HasSheafCompose (forget RingCat.{wT})]
  [T'.J.HasSheafCompose (forget RingCat.{wT'})]
  [P.J.HasSheafCompose (forget₂ CommRingCat.{wP} RingCat.{wP})]
  [Q.J.HasSheafCompose (forget₂ CommRingCat.{wQ} RingCat.{wQ})]
  [R.J.HasSheafCompose (forget₂ CommRingCat.{wR} RingCat.{wR})]
  [R'.J.HasSheafCompose (forget₂ CommRingCat.{wR'} RingCat.{wR'})]
  [T.J.HasSheafCompose (forget₂ CommRingCat.{wT} RingCat.{wT})]
  [T'.J.HasSheafCompose (forget₂ CommRingCat.{wT'} RingCat.{wT'})]

/-- **A composite of conjugates is the conjugate of the composite.**  Let `m : R ⟶ R'` and
`m' : R' ⟶ R` be morphisms of ringed topoi with `m' ∘ m` 2-isomorphic to the identity of `R`.
Then for `a' : P ⟶ Q`, `ρ : Q ⟶ R`, `χ : R ⟶ T` and `b : T ⟶ T'` the composite
`(b ∘ χ ∘ m') ∘ (m ∘ ρ ∘ a')` of the two conjugates is 2-isomorphic to the conjugate
`b ∘ (χ ∘ ρ) ∘ a'` of the composite: the `m' ∘ m` sitting between the two halves cancels.

Only `m' ∘ m ≅ 1_R` is needed; neither `m` nor `m'` has to be invertible in any stronger
sense. -/
noncomputable def TwoIso.compConjugate {a' : RingedToposHom P Q} {ρ : RingedToposHom Q R}
    {m : RingedToposHom R R'} {m' : RingedToposHom R' R} {χ : RingedToposHom R T}
    {b : RingedToposHom T T'}
    (η : TwoIso (m'.comp m) (RingedToposHom.id R)) :
    TwoIso ((b.comp (χ.comp m')).comp (m.comp (ρ.comp a')))
      (b.comp ((χ.comp ρ).comp a')) :=
  (TwoIso.associator (m.comp (ρ.comp a')) (χ.comp m') b).symm.trans
    (TwoIso.whiskerRight
      ((TwoIso.associator (m.comp (ρ.comp a')) m' χ).symm.trans
        ((TwoIso.whiskerRight
            ((TwoIso.associator (ρ.comp a') m m').trans
              ((TwoIso.whiskerLeft (ρ.comp a') η).trans
                (TwoIso.idComp (ρ.comp a')))) χ).trans
          (TwoIso.associator a' ρ χ))) b)

end CompConjugation

end AlgebraicGeometry.RingedToposHom

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U W V : BigFppfOver B S hS)

/-- **The conjugation of `AlgebraicGeometry.Space.schemeOfRepresentedRingedToposHom` is
compatible with composition.**  The composite of the conjugates of `ρ` and `χ` is 2-isomorphic
to the conjugate of `χ ∘ ρ`.

The composite of the conjugates carries, between its two halves, the identification of the
middle chart `W` taken first from the space side and then from the scheme side; that composite
is 2-isomorphic to the identity by
`AlgebraicGeometry.Space.representedSmallEtaleRingedToposInverseComp`, and cancelling it is the
whole content, which is
`AlgebraicGeometry.RingedToposHom.TwoIso.compConjugate`. -/
noncomputable def schemeOfRepresentedRingedToposHomComp
    (ρ : RingedToposHom
      (smallEtaleRingedTopos B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
      (smallEtaleRingedTopos B S hS ⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩))
    (χ : RingedToposHom
      (smallEtaleRingedTopos B S hS ⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩)
      (smallEtaleRingedTopos B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩)) :
    RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u}
      (RingedToposHom.comp.{u, u + 1, u, u, u + 1, u, u, u + 1, u}
        (schemeOfRepresentedRingedToposHom B S hS W V χ)
        (schemeOfRepresentedRingedToposHom B S hS U W ρ))
      (schemeOfRepresentedRingedToposHom B S hS U V
        (RingedToposHom.comp.{u, u + 1, u, u, u + 1, u, u, u + 1, u} χ ρ)) :=
  RingedToposHom.TwoIso.compConjugate
    (a' := representedSmallEtaleRingedToposInverse B S hS U)
    (ρ := ρ)
    (m := representedSmallEtaleRingedToposHom B S hS W)
    (m' := representedSmallEtaleRingedToposInverse B S hS W)
    (χ := χ)
    (b := representedSmallEtaleRingedToposHom B S hS V)
    (representedSmallEtaleRingedToposInverseComp B S hS W)

end AlgebraicGeometry.Space

end
