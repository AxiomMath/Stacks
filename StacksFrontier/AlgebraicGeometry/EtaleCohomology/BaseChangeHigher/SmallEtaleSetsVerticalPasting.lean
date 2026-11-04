module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.OrdinaryLocality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.OrdinaryLocalityCoefficients
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.SmallEtaleBaseChangePasting
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.SmallEtaleVerticalPasting

/-!
# Pasting of the base change map of sheaves of sets along the direct image legs

Let

```
X' --g'--> X
|p'         |p
v           v
X'_1 --gi--> X_1
|st'         |st
v            v
Y' --g-->   Y
```

be two commutative squares of schemes sharing the edge `gi`, so that `g' ≫ p = p' ≫ gi` and
`gi ≫ st = st' ≫ g`, and let `f = p ≫ st`, `f' = p' ≫ st'` be the two composite vertical legs.
The outer rectangle commutes, and this file proves that the base change map
`Stacks.EtaleCohomology.smallEtaleSetsBaseChange` of the outer rectangle is the composite of the
base change maps of the two squares, read through the comparisons
`Stacks.EtaleCohomology.smallEtalePushforwardComp'` of the direct images along `f = p ≫ st` and
`f' = p' ≫ st'`.

This is the *vertical* pasting law — pasting in the direction of the direct images — for sheaves
of **sets**. The library already carries it for abelian coefficients, as
`Stacks.EtaleCohomology.smallEtaleBaseChangeAb_vpaste`, and the pasting law in the other
direction, along the inverse image legs, as
`Stacks.EtaleCohomology.smallEtaleBaseChangeAb_paste`; the proof below is the sets-valued twin of
the first of those and reuses both of its two inputs that do not mention the coefficients: the
naturality `Stacks.EtaleCohomology.mateEquiv_whiskerTop_whiskerBottom` of Mathlib's mates
equivalence in the two vertical legs of a square, and the cancellation
`Stacks.EtaleCohomology.paste_algebra` of fourteen morphisms in an abstract category.

## Main results

* `Stacks.EtaleCohomology.smallEtalePushforwardComp'_assoc_app` — the associativity pentagon of
  the comparison of direct images, at arbitrary coefficients and evaluated at a sheaf. The
  library carried only its inverse form,
  `Stacks.EtaleCohomology.smallEtalePushforwardComp'_inv_app_cocycle`, and the abelian
  specialization `Stacks.EtaleCohomology.smallEtalePushforwardAbComp'_assoc_app`.
* `Stacks.EtaleCohomology.smallEtalePushforwardComp'_eq` and
  `Stacks.EtaleCohomology.smallEtalePushforwardComp'_rfl` — the two vocabularies for the
  comparison of direct images along a composite agree, at arbitrary coefficients.
* `Stacks.EtaleCohomology.smallEtaleSquarePushforwardIsoAt_eq_comp'` — the square comparison of
  direct images, written with the diagonal of the square *named*. This is the form the
  associativity pentagon can be applied to.
* `Stacks.EtaleCohomology.mateEquiv_smallEtaleSetsBaseChange` — the mate of the base change map
  of sheaves of sets is the square comparison of direct images.
* `Stacks.EtaleCohomology.smallEtaleSquarePushforwardIsoAt_vpaste_app` — the vertical pasting of
  the square comparisons of direct images, the geometric content.
* `Stacks.EtaleCohomology.smallEtaleSetsBaseChange_vpaste` and
  `Stacks.EtaleCohomology.smallEtaleSetsBaseChange_vpaste_app` — **the pasting law**, as an
  identity of 2-squares and evaluated at a sheaf.

## Implementation notes

*The composites are named.* Every statement below takes the diagonal of a square, or the
composite of two vertical legs, as a named morphism together with an equation identifying it,
rather than writing it out. This is the convention of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/DirectImageSystem.lean`, and it is what
makes the law applicable at a limit presentation of a square, where the two vertical legs `f`,
`f'` of the outer rectangle are *given* morphisms and the factorizations `f = p ≫ st`,
`f' = p' ≫ st'` are equations of the presentation rather than definitions. The abelian twin
writes the composites out and therefore needs
`Stacks.EtaleCohomology.smallEtalePushforwardAbComp'_rfl` at every use.

*The six corners are explicit arguments.* `X`, `X'`, `Xi`, `Xi'`, `Y`, `Y'` are passed by hand at
every use rather than left to unification. At a limit presentation of the square the structure
morphisms are components of natural transformations to constant functors, so the type of
`st = st_i` is `X_i ⟶ ((Functor.const _).obj Y).obj i`; left implicit, the corner `Y` is then
solved as that projection rather than as `Y`, every occurrence of `Y` in the conclusion — the
topology, the base change map, the coefficients — inherits it, and matching the instance against a
goal written with `Y` forces the kernel to reduce
`Stacks.EtaleCohomology.smallEtaleSetsBaseChange`, the mate of the square comparison of composite
direct images, inside those corners. Supplied explicitly, the corner is checked once, on its own,
and the instance is syntactically the goal. This is the convention of
`Stacks.EtaleCohomology.isIso_smallEtaleSetsBaseChange_app_of_isFinite` and of
`Stacks.EtaleCohomology.stageComparison_comp_stageLeg`, its one consumer.

*No tag is placed.* [Stacks, Tag 0E46] states the pasting law for ringed topoi and the derived
base change map; what is proved here is the underived identity for sheaves of sets, one
ingredient of that statement rather than the statement itself.

## References

* [Stacks Project, Tag 0E46](https://stacks.math.columbia.edu/tag/0E46)
* [Stacks Project, Tag 0F02](https://stacks.math.columbia.edu/tag/0F02)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v w t

namespace Stacks.EtaleCohomology

/-! ### The associativity pentagon, evaluated at a sheaf -/

/-- **The associativity pentagon of the comparison of direct images, evaluated at a sheaf**, at
arbitrary coefficients: this is `Stacks.EtaleCohomology.smallEtalePushforwardComp'_assoc` with the
associators, which are identities on components, cancelled.

The library carried the inverse form of this identity,
`Stacks.EtaleCohomology.smallEtalePushforwardComp'_inv_app_cocycle`, and the abelian
specialization of this one,
`Stacks.EtaleCohomology.smallEtalePushforwardAbComp'_assoc_app`; the pasting argument below
consumes the hom form at sheaves of sets. -/
theorem smallEtalePushforwardComp'_assoc_app {T X Y Z : Scheme.{u}} (f : T ⟶ X) (g : X ⟶ Y)
    (h : Y ⟶ Z) (fg : T ⟶ Y) (hfg : fg = f ≫ g) (gh : X ⟶ Z) (hgh : gh = g ≫ h)
    (fgh : T ⟶ Z) (h₁ : fgh = fg ≫ h) (h₂ : fgh = f ≫ gh) (A : Type w) [Category.{t} A]
    (F : Sheaf (smallEtaleTopology T) A) :
    (smallEtalePushforward h A).map ((smallEtalePushforwardComp' f g fg hfg A).hom.app F) ≫
        (smallEtalePushforwardComp' fg h fgh h₁ A).hom.app F =
      (smallEtalePushforwardComp' g h gh hgh A).hom.app ((smallEtalePushforward f A).obj F) ≫
        (smallEtalePushforwardComp' f gh fgh h₂ A).hom.app F := by
  have h0 := congrArg (fun z : _ ≅ _ => NatTrans.app z.hom F)
    (smallEtalePushforwardComp'_assoc f g h fg hfg gh hgh fgh h₁ h₂ A)
  simpa using h0

/-! ### The two vocabularies for the comparison along a composite -/

section Vocabulary

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- **The two vocabularies for the comparison of direct images agree**, at arbitrary
coefficients: the named-composite form
`Stacks.EtaleCohomology.smallEtalePushforwardComp'` is the written-out form
`Stacks.EtaleCohomology.smallEtalePushforwardCompIsoAt` followed by the transport along the
naming equation. -/
theorem smallEtalePushforwardComp'_eq (fg : X ⟶ Z) (hfg : fg = f ≫ g) (A : Type w)
    [Category.{t} A] :
    smallEtalePushforwardComp' f g fg hfg A =
      smallEtalePushforwardCompIsoAt f g A ≪≫
        eqToIso (congrArg (fun k : X ⟶ Z => smallEtalePushforwardAt k A) hfg.symm) := by
  subst hfg
  have hbc : smallEtaleBaseChangeComp' f g (f ≫ g) rfl = smallEtaleBaseChangeComp f g := by
    simp [smallEtaleBaseChangeComp']
  simp only [smallEtalePushforwardComp', hbc, smallEtalePushforwardCompIsoAt, eqToIso_refl]
  exact (Iso.trans_refl _).symm

/-- At a literal composite the two vocabularies coincide. -/
theorem smallEtalePushforwardComp'_rfl (A : Type w) [Category.{t} A] :
    smallEtalePushforwardComp' f g (f ≫ g) rfl A = smallEtalePushforwardCompIsoAt f g A := by
  rw [smallEtalePushforwardComp'_eq]
  simp

end Vocabulary

/-! ### The square comparison of direct images, with the diagonal named -/

/-- **The square comparison of direct images with the diagonal of the square named.** For a
commutative square `e ≫ g = h ≫ f` and a morphism `d` identified with both composites, the
identification `Stacks.EtaleCohomology.smallEtaleSquarePushforwardIsoAt` of the two composite
direct images is the comparison along `d = e ≫ g` followed by the inverse of the comparison along
`d = h ≫ f`.

This is the form `Stacks.EtaleCohomology.smallEtalePushforwardComp'_assoc_app` applies to: the
definition of the square comparison glues the commutativity of the square in by `eqToIso`,
whereas the associativity pentagon is stated for named composites. -/
theorem smallEtaleSquarePushforwardIsoAt_eq_comp' {Y T X S : Scheme.{u}} (e : Y ⟶ T) (h : Y ⟶ X)
    (g : T ⟶ S) (f : X ⟶ S) (hcomm : e ≫ g = h ≫ f) (d : Y ⟶ S) (hd₁ : d = e ≫ g)
    (hd₂ : d = h ≫ f) (A : Type w) [Category.{t} A] :
    smallEtaleSquarePushforwardIsoAt e h g f hcomm A =
      smallEtalePushforwardComp' e g d hd₁ A ≪≫
        (smallEtalePushforwardComp' h f d hd₂ A).symm := by
  subst hd₂
  rw [smallEtaleSquarePushforwardIsoAt, smallEtalePushforwardComp'_eq e g (h ≫ f) hd₁,
    smallEtalePushforwardComp'_rfl]
  simp [Iso.trans_assoc]

/-! ### The mate of the base change map -/

/-- **The mate of the base change map of sheaves of sets is the square comparison of direct
images.** This is the bridge that makes Mathlib's pasting lemmas for `CategoryTheory.mateEquiv`
applicable: the base change map is by definition the inverse mate of the square comparison, so
the identity to be proved for the base change maps becomes an identity between comparisons of
composite direct images. -/
theorem mateEquiv_smallEtaleSetsBaseChange {X' X Y' Y : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (f : X ⟶ Y) (g : Y' ⟶ Y) (w : g' ≫ f = f' ≫ g) :
    mateEquiv (smallEtaleSetsAdjunction.{u, v} g') (smallEtaleSetsAdjunction.{u, v} g)
        (TwoSquare.mk _ _ _ _ (smallEtaleSetsBaseChange.{u, v} g' f' f g w)) =
      TwoSquare.mk _ _ _ _
        (smallEtaleSquarePushforwardIsoAt g' f' f g w (Type (max (u + 1) v))).hom :=
  (mateEquiv (smallEtaleSetsAdjunction.{u, v} g')
    (smallEtaleSetsAdjunction.{u, v} g)).apply_symm_apply _

/-! ### The pasting law -/

section VPaste

variable (X X' Xi Xi' Y Y' : Scheme.{u}) (g' : X' ⟶ X) (p : X ⟶ Xi) (p' : X' ⟶ Xi')
  (gi : Xi' ⟶ Xi) (st : Xi ⟶ Y) (st' : Xi' ⟶ Y') (g : Y' ⟶ Y) (f : X ⟶ Y) (hf : f = p ≫ st)
  (f' : X' ⟶ Y') (hf' : f' = p' ≫ st') (w₁ : g' ≫ p = p' ≫ gi) (w₂ : gi ≫ st = st' ≫ g)
  (w : g' ≫ f = f' ≫ g)

/-- **The vertical pasting of the square comparisons of direct images**, which is the geometric
content of the pasting law. The comparison of the two composite direct images around the outer
rectangle is the composite of the comparisons of the two squares, read through the comparisons of
the direct images along the two composite vertical legs `f = p ≫ st` and `f' = p' ≫ st'`.

The only input is the associativity pentagon
`Stacks.EtaleCohomology.smallEtalePushforwardComp'_assoc_app`, applied to the three threefold
composites `(g', p, st)`, `(p', gi, st)` and `(p', st', g)` through the rectangle; the
rearrangement that turns those three instances into this identity is
`Stacks.EtaleCohomology.paste_algebra`, the same cancellation the two abelian pasting laws
use. -/
theorem smallEtaleSquarePushforwardIsoAt_vpaste_app (A : Type w) [Category.{t} A]
    (𝒢 : Sheaf (smallEtaleTopology X') A) :
    (smallEtaleSquarePushforwardIsoAt g' f' f g w A).hom.app 𝒢 =
      (smallEtalePushforwardComp' p st f hf A).inv.app
          ((smallEtalePushforward g' A).obj 𝒢) ≫
        (smallEtalePushforward st A).map
            ((smallEtaleSquarePushforwardIsoAt g' p' p gi w₁ A).hom.app 𝒢) ≫
          (smallEtaleSquarePushforwardIsoAt gi st' st g w₂ A).hom.app
              ((smallEtalePushforward p' A).obj 𝒢) ≫
            (smallEtalePushforward g A).map
              ((smallEtalePushforwardComp' p' st' f' hf' A).hom.app 𝒢) := by
  have hd₁ : g' ≫ f = (g' ≫ p) ≫ st := by rw [hf, Category.assoc]
  have hd₂ : g' ≫ f = p' ≫ gi ≫ st := by rw [hd₁, w₁, Category.assoc]
  have hP₁ := smallEtalePushforwardComp'_assoc_app g' p st (g' ≫ p) rfl f hf (g' ≫ f) hd₁ rfl A 𝒢
  have hP₂ := smallEtalePushforwardComp'_assoc_app p' gi st (g' ≫ p) w₁ (gi ≫ st) rfl (g' ≫ f)
    hd₁ hd₂ A 𝒢
  have hP₃ := smallEtalePushforwardComp'_assoc_app p' st' g f' hf' (gi ≫ st) w₂ (g' ≫ f) w hd₂
    A 𝒢
  rw [smallEtaleSquarePushforwardIsoAt_eq_comp' g' f' f g w (g' ≫ f) rfl w A,
    smallEtaleSquarePushforwardIsoAt_eq_comp' g' p' p gi w₁ (g' ≫ p) rfl w₁ A,
    smallEtaleSquarePushforwardIsoAt_eq_comp' gi st' st g w₂ (gi ≫ st) rfl w₂ A]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.map_comp, Category.assoc]
  refine paste_algebra ?_ ?_ ?_ ?_ hP₁.symm hP₂.symm hP₃.symm
  · exact Iso.inv_hom_id_app _ _
  · exact Iso.hom_inv_id_app _ _
  · rw [← Functor.map_comp, Iso.inv_hom_id_app]
    exact CategoryTheory.Functor.map_id _ _
  · exact Iso.inv_hom_id_app _ _

/-- **The vertical pasting law for the base change map of sheaves of sets.** For two commutative
squares of schemes composed along their direct image legs, the base change map of the outer
rectangle is the base change map of the lower square followed by the direct image of the base
change map of the upper square, read through the comparisons of the direct images along the two
composite legs `f = p ≫ st` and `f' = p' ≫ st'`.

The hypotheses are the commutativity of the two squares and the two factorizations, and nothing
else: neither square need be cartesian, and no finiteness or separatedness condition enters. -/
theorem smallEtaleSetsBaseChange_vpaste :
    TwoSquare.mk _ _ _ _ (smallEtaleSetsBaseChange.{u, v} g' f' f g w) =
      (((TwoSquare.mk _ _ _ _
                (smallEtaleSetsBaseChange.{u, v} g' p' p gi w₁)).hComp
              (TwoSquare.mk _ _ _ _
                (smallEtaleSetsBaseChange.{u, v} gi st' st g w₂))).whiskerTop
            (smallEtalePushforwardComp' p st f hf (Type (max (u + 1) v))).inv).whiskerBottom
        (smallEtalePushforwardComp' p' st' f' hf' (Type (max (u + 1) v))).hom := by
  apply (mateEquiv (smallEtaleSetsAdjunction.{u, v} g')
    (smallEtaleSetsAdjunction.{u, v} g)).injective
  rw [mateEquiv_whiskerTop_whiskerBottom,
    mateEquiv_vcomp (smallEtaleSetsAdjunction.{u, v} g') (smallEtaleSetsAdjunction.{u, v} gi)
      (smallEtaleSetsAdjunction.{u, v} g),
    mateEquiv_smallEtaleSetsBaseChange, mateEquiv_smallEtaleSetsBaseChange,
    mateEquiv_smallEtaleSetsBaseChange]
  refine TwoSquare.ext _ _ fun 𝒢 => ?_
  simpa using smallEtaleSquarePushforwardIsoAt_vpaste_app X X' Xi Xi' Y Y' g' p p' gi st st' g f
    hf f' hf' w₁ w₂ w (Type (max (u + 1) v)) 𝒢

/-- **The vertical pasting law for the base change map of sheaves of sets, evaluated at a
sheaf.** -/
theorem smallEtaleSetsBaseChange_vpaste_app
    (F : Sheaf (smallEtaleTopology X) (Type (max (u + 1) v))) :
    (smallEtaleSetsBaseChange.{u, v} g' f' f g w).app F =
      (smallEtaleInverseImage.{u, v} g).map
          ((smallEtalePushforwardComp' p st f hf (Type (max (u + 1) v))).inv.app F) ≫
        (smallEtaleSetsBaseChange.{u, v} gi st' st g w₂).app
            ((smallEtalePushforward p (Type (max (u + 1) v))).obj F) ≫
          (smallEtaleDirectImage.{u, v} st').map
              ((smallEtaleSetsBaseChange.{u, v} g' p' p gi w₁).app F) ≫
            (smallEtalePushforwardComp' p' st' f' hf' (Type (max (u + 1) v))).hom.app
              ((smallEtaleInverseImage.{u, v} g').obj F) := by
  have h := congr_app (smallEtaleSetsBaseChange_vpaste.{u, v} X X' Xi Xi' Y Y' g' p p' gi st st' g
    f hf f' hf' w₁ w₂ w) F
  simpa using h

/-- **The vertical pasting law with the comparison of the direct images along `f = p ≫ st` moved
to the left.** This is `Stacks.EtaleCohomology.smallEtaleSetsBaseChange_vpaste_app` with the
inverse of that comparison cancelled against its hom, and it is the form a limit presentation of
the square consumes: there `f` is a given morphism, the identification of `f_* F` with
`st_*p_*F` is a morphism of the presentation rather than something to be inverted, and the right
hand side is literally the stagewise comparison followed by the stagewise leg.

It is stated here, about plain variables, rather than derived at each use: with the stages of an
inverse system substituted for the four corners of the two squares the arguments of
`Stacks.EtaleCohomology.smallEtaleSetsBaseChange` are large terms, and the kernel does not get
through the defeq check of the resulting identity — the same reason
`Stacks.EtaleCohomology.isIso_smallEtaleSetsBaseChange_app_of_isFinite` is stated about
variables. -/
theorem smallEtaleSetsBaseChange_vpaste_app'
    (F : Sheaf (smallEtaleTopology X) (Type (max (u + 1) v))) :
    (smallEtaleInverseImage.{u, v} g).map
          ((smallEtalePushforwardComp' p st f hf (Type (max (u + 1) v))).hom.app F) ≫
        (smallEtaleSetsBaseChange.{u, v} g' f' f g w).app F =
      (smallEtaleSetsBaseChange.{u, v} gi st' st g w₂).app
          ((smallEtalePushforward p (Type (max (u + 1) v))).obj F) ≫
        (smallEtaleDirectImage.{u, v} st').map
            ((smallEtaleSetsBaseChange.{u, v} g' p' p gi w₁).app F) ≫
          (smallEtalePushforwardComp' p' st' f' hf' (Type (max (u + 1) v))).hom.app
            ((smallEtaleInverseImage.{u, v} g').obj F) := by
  rw [smallEtaleSetsBaseChange_vpaste_app.{u, v} X X' Xi Xi' Y Y' g' p p' gi st st' g f hf f' hf'
      w₁ w₂ w F,
    ← Iso.app_hom, ← Iso.app_inv,
    ← Functor.mapIso_hom (smallEtaleInverseImage.{u, v} g),
    ← Functor.mapIso_inv (smallEtaleInverseImage.{u, v} g), Iso.hom_inv_id_assoc]

end VPaste

end Stacks.EtaleCohomology

end
