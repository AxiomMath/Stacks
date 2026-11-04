module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModulePullbackConjugate
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModulePushforwardSquareComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalAugmentationForkInverseImage

/-!
# The pasting coherence of the square of inverse images of a representable morphism

`AlgebraicGeometry.Space.representedModulePullbackIso` compares, for a morphism `g : T' ⟶ T` of
the big fppf category over `S`, the two routes round the square of small étale ringed sites on
the pullback side: reading a sheaf of modules on the small étale site of the scheme underlying
`T` on the small étale site of `yoneda.obj T` and then taking the inverse image of Stacks 03LU
along the represented morphism, against pulling it back along the morphism of ringed sites of
Stacks 070R (2) attached to the underlying morphism of schemes and then reading the result.
This file proves that those squares paste: for `h : T'' ⟶ T'` and `g : T' ⟶ T`, pasting the
square of `h` against the square of `g` and contracting the two inverse images on each side
gives the square of `h ≫ g`.

Both sides of the square are *left* adjoints, so neither has a formula and the coherence cannot
be proved by computing with sections.  What determines such an isomorphism is its mate: the
conjugate of the square of inverse images is the square of direct images
(`AlgebraicGeometry.Space.conjugateEquiv_representedModulePullbackIso_hom`), and
`CategoryTheory.conjugateEquiv` is a bijection compatible with composition and with whiskering.
So conjugating the coherence turns it into the corresponding coherence for the direct images,
which is `AlgebraicGeometry.Space.representedModulePushforwardSquareIso_comp`.

## Main definitions

* `AlgebraicGeometry.Space.representedModulePullbackCompIso` and
  `AlgebraicGeometry.Space.representedSchemeModulePullbackCompIso` contract the two inverse
  images on the two sides of the square — the first the inverse images of Stacks 03LU along the
  represented morphisms, the second the pullbacks along the morphisms of ringed sites of
  Stacks 070R (2).

## Main results

* `Stacks.Mates.pastedSquare_eq_of_conjugate`: **a pasting of squares of left adjoints follows
  from the corresponding pasting of their mates**, at arbitrary categories, given the conjugate
  of each of the five isomorphisms involved.
* `AlgebraicGeometry.Space.conjugateEquiv_representedModulePullbackCompIso` and
  `AlgebraicGeometry.Space.conjugateEquiv_representedSchemeModulePullbackCompIso`: the two
  contractions of inverse images are conjugate to the two contractions of direct images.
* `AlgebraicGeometry.Space.representedModulePullbackIso_comp`: **the square of inverse images
  of a representable morphism satisfies the pasting coherence.**

## Implementation notes

The whole reduction is carried out at arbitrary categories by
`Stacks.Mates.pastedSquare_eq_of_conjugate`, whose hypotheses are the conjugate of each
isomorphism of the diagram and the pasting coherence of the mates, and whose instantiation here
matches only functors and adjunctions.  This keeps the composite adjunctions of the square out
of every rewrite: composition in the category of `𝒪`-modules of an algebraic space is a
projection of the `SheafOfModules` instance, so a step that unfolds it under `≫` is
unaffordable, while a step that only matches an adjunction against a variable is free.  For the
same reason the coherence is stated as an equality of isomorphisms rather than of morphisms of
functors.

The reduction needs the comparison of the two nestings of a threefold composite of adjunctions,
which `CategoryTheory.Adjunction.comp_assoc` supplies as an equality of adjunctions: the
underlying functors of the two nestings are equal, the associators of functors being
identities, so the two differ only in the spelling of the unit, and `conjugateEquiv` can be
rewritten from one to the other.

The two contractions of inverse images are characterised in opposite orientations, which is
what `Stacks.CategoryTheory.conjugateEquiv_inv_of_hom` reconciles:
`AlgebraicGeometry.Space.modulePullbackCompIso` is
`CategoryTheory.Adjunction.leftAdjointUniq` with the transported adjunction *first*, so
`Stacks.CategoryTheory.conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom` characterises it on
its morphism, while `AlgebraicGeometry.SmallEtale.smallEtalePullbackCompIso` has it *second*
and `AlgebraicGeometry.SmallEtale.conjugateEquiv_smallEtalePullbackCompIso_inv` characterises
it on its inverse.

The composite of the morphisms of algebraic spaces represented by `h` and by `g` is only
provably the morphism represented by `h ≫ g`
(`AlgebraicGeometry.Space.representedSpaceMap_comp`), so the contraction of the two inverse
images of Stacks 03LU carries the `eqToIso` of that equality, exactly as
`AlgebraicGeometry.Space.representedModulePushforwardCompIso` does; the conjugate of such a
transport is `Stacks.CategoryTheory.conjugateEquiv_eqToHom`.

No scoped reducibility device is needed here, unlike in
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedModulePullbackConjugate.lean` and
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedModulePushforwardSquareComp.lean`, where
`AlgebraicGeometry.Space.smallEtaleRingedSite` is made locally `implicit_reducible` so that the
two spellings of the category of `𝒪`-modules agree for instance search.  Every adjunction and
every isomorphism of the square is supplied to the reduction as an explicit term taken from
those two files, so nothing has to be found by instance search.

No tag is registered.  Stacks 03LU is tagged where
`AlgebraicGeometry.Space.modulePullbackCompIso` is proved; what is added here is that the
identification of
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedModulePullbackBaseChange.lean` is functorial
in the morphism on the pullback side.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
-/

@[expose] public section

open CategoryTheory

namespace Stacks.CategoryTheory

variable {C₀ C₁ : Type*} [Category* C₀] [Category* C₁]

/-- **The conjugate of a transport along an equality of indices.**  For a family of adjunctions
indexed by `ι` and an equality `i = j` of indices, the transport of the left adjoints has the
transport of the right adjoints as its conjugate.  Both are `eqToHom` of the equality the index
equality induces, and the statement is the index equality substituted away. -/
theorem conjugateEquiv_eqToHom {ι : Type*} (L : ι → (C₀ ⥤ C₁)) (R : ι → (C₁ ⥤ C₀))
    (adj : ∀ i, L i ⊣ R i) {i j : ι} (hij : i = j) :
    conjugateEquiv (adj j) (adj i) (eqToHom (congrArg L hij)) =
      eqToHom (congrArg R hij.symm) := by
  subst hij
  simp

end Stacks.CategoryTheory

namespace Stacks.Mates

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

variable {A : Type u₁} [Category.{v₁} A] {A' : Type u₂} [Category.{v₂} A']
  {A'' : Type u₃} [Category.{v₃} A''] {D : Type u₄} [Category.{v₄} D]
  {D' : Type u₅} [Category.{v₅} D'] {D'' : Type u₆} [Category.{v₆} D'']

/-- **A pasting of squares of left adjoints follows from the pasting of their mates.**

Consider two squares of left adjoints side by side,
```
      A --LPg--> A' --LPh--> A''
      |           |            |
     LE          LE'          LE''
      ↓            ↓            ↓
      D --LQg--> D' --LQh--> D''
```
together with contractions `cP : LPg ⋙ LPh ≅ LPk` and `cQ : LQg ⋙ LQh ≅ LQk` of the two rows
and a square `sqPk` for the contracted row.  Suppose every functor of the two rows and every
vertical functor is a left adjoint, and let `sqRg`, `sqRh`, `sqRk`, `cR`, `dR` be the mates of
the three squares and the two contractions.  If the mates paste, so do the squares.

`CategoryTheory.conjugateEquiv` is a bijection, so it suffices to compare the conjugates of the
two sides; it is compatible with composition and with whiskering on either side, so each factor
of the pasting is conjugated separately, by hypothesis.  The only bookkeeping is the nesting of
the threefold composite adjunctions, which `CategoryTheory.Adjunction.comp_assoc` normalises. -/
theorem pastedSquare_eq_of_conjugate
    {LPg : A ⥤ A'} {RPg : A' ⥤ A} {LPh : A' ⥤ A''} {RPh : A'' ⥤ A'}
    {LPk : A ⥤ A''} {RPk : A'' ⥤ A}
    {LQg : D ⥤ D'} {RQg : D' ⥤ D} {LQh : D' ⥤ D''} {RQh : D'' ⥤ D'}
    {LQk : D ⥤ D''} {RQk : D'' ⥤ D}
    {LE : A ⥤ D} {RE : D ⥤ A} {LE' : A' ⥤ D'} {RE' : D' ⥤ A'}
    {LE'' : A'' ⥤ D''} {RE'' : D'' ⥤ A''}
    (adjPg : LPg ⊣ RPg) (adjPh : LPh ⊣ RPh) (adjPk : LPk ⊣ RPk)
    (adjQg : LQg ⊣ RQg) (adjQh : LQh ⊣ RQh) (adjQk : LQk ⊣ RQk)
    (adjE : LE ⊣ RE) (adjE' : LE' ⊣ RE') (adjE'' : LE'' ⊣ RE'')
    (sqPg : LPg ⋙ LE' ≅ LE ⋙ LQg) (sqPh : LPh ⋙ LE'' ≅ LE' ⋙ LQh)
    (sqPk : LPk ⋙ LE'' ≅ LE ⋙ LQk)
    (cP : LPg ⋙ LPh ≅ LPk) (cQ : LQg ⋙ LQh ≅ LQk)
    (sqRg : RQg ⋙ RE ≅ RE' ⋙ RPg) (sqRh : RQh ⋙ RE' ≅ RE'' ⋙ RPh)
    (sqRk : RQk ⋙ RE ≅ RE'' ⋙ RPk)
    (cR : RPh ⋙ RPg ≅ RPk) (dR : RQh ⋙ RQg ≅ RQk)
    (hg : conjugateEquiv (adjE.comp adjQg) (adjPg.comp adjE') sqPg.hom = sqRg.hom)
    (hh : conjugateEquiv (adjE'.comp adjQh) (adjPh.comp adjE'') sqPh.hom = sqRh.hom)
    (hk : conjugateEquiv (adjE.comp adjQk) (adjPk.comp adjE'') sqPk.hom = sqRk.hom)
    (hcP : conjugateEquiv adjPk (adjPg.comp adjPh) cP.hom = cR.inv)
    (hcQ : conjugateEquiv adjQk (adjQg.comp adjQh) cQ.hom = dR.inv)
    (hpaste : Functor.isoWhiskerLeft RQh sqRg ≪≫ Functor.isoWhiskerRight sqRh RPg ≪≫
          Functor.isoWhiskerLeft RE'' cR =
        Functor.isoWhiskerRight dR RE ≪≫ sqRk) :
    Functor.isoWhiskerLeft LPg sqPh ≪≫ Functor.isoWhiskerRight sqPg LQh ≪≫
        Functor.isoWhiskerLeft LE cQ =
      Functor.isoWhiskerRight cP LE'' ≪≫ sqPk := by
  have hu : conjugateEquiv (adjE.comp adjQk) (adjE.comp (adjQg.comp adjQh))
      (Functor.whiskerLeft LE cQ.hom) = Functor.whiskerRight dR.inv RE := by
    rw [conjugateEquiv_whiskerLeft, hcQ]
  have hv : conjugateEquiv (adjE.comp (adjQg.comp adjQh)) (adjPg.comp (adjE'.comp adjQh))
      (Functor.whiskerRight sqPg.hom LQh) = Functor.whiskerLeft RQh sqRg.hom := by
    rw [Adjunction.comp_assoc adjE adjQg adjQh, Adjunction.comp_assoc adjPg adjE' adjQh,
      conjugateEquiv_whiskerRight, hg]
  have hw : conjugateEquiv (adjPg.comp (adjE'.comp adjQh)) (adjPg.comp (adjPh.comp adjE''))
      (Functor.whiskerLeft LPg sqPh.hom) = Functor.whiskerRight sqRh.hom RPg := by
    rw [conjugateEquiv_whiskerLeft, hh]
  have hc : conjugateEquiv (adjPk.comp adjE'') ((adjPg.comp adjPh).comp adjE'')
      (Functor.whiskerRight cP.hom LE'') = Functor.whiskerLeft RE'' cR.inv := by
    rw [conjugateEquiv_whiskerRight, hcP]
  have hLHS : conjugateEquiv (adjE.comp adjQk) ((adjPg.comp adjPh).comp adjE'')
        (Functor.isoWhiskerLeft LPg sqPh ≪≫ Functor.isoWhiskerRight sqPg LQh ≪≫
          Functor.isoWhiskerLeft LE cQ).hom =
      Functor.whiskerRight dR.inv RE ≫
        Functor.whiskerLeft RQh sqRg.hom ≫ Functor.whiskerRight sqRh.hom RPg := by
    rw [Iso.trans_hom, Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, ← Adjunction.comp_assoc adjPg adjPh adjE'',
      ← conjugateEquiv_comp (adjE.comp adjQk) (adjPg.comp (adjE'.comp adjQh))
        (adjPg.comp (adjPh.comp adjE'')), hw,
      ← conjugateEquiv_comp (adjE.comp adjQk) (adjE.comp (adjQg.comp adjQh))
        (adjPg.comp (adjE'.comp adjQh)), hu, hv, Category.assoc]
  have hRHS : conjugateEquiv (adjE.comp adjQk) ((adjPg.comp adjPh).comp adjE'')
        (Functor.isoWhiskerRight cP LE'' ≪≫ sqPk).hom =
      sqRk.hom ≫ Functor.whiskerLeft RE'' cR.inv := by
    rw [Iso.trans_hom, Functor.isoWhiskerRight_hom,
      ← conjugateEquiv_comp (adjE.comp adjQk) (adjPk.comp adjE'')
        ((adjPg.comp adjPh).comp adjE''), hk, hc]
  refine Iso.ext ((conjugateEquiv (adjE.comp adjQk)
    ((adjPg.comp adjPh).comp adjE'')).injective ?_)
  rw [hLHS, hRHS, ← Functor.isoWhiskerRight_inv, ← Functor.isoWhiskerLeft_inv,
    Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  have hp := congrArg Iso.hom hpaste
  simp only [Iso.trans_hom] at hp
  rw [Category.assoc]
  exact hp

end Stacks.Mates

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Represented

variable {T'' T' T : BigFppfOver B S hS} (h : T'' ⟶ T') (g : T' ⟶ T)
  (hh : yoneda.relativelyRepresentable (yoneda.map h))
  (hg : yoneda.relativelyRepresentable (yoneda.map g))
  (hhg : yoneda.relativelyRepresentable (yoneda.map (h ≫ g)))

/-- The contraction of the two inverse images of Stacks 03LU along the represented morphisms, at
the morphism represented by the composite.  The transport is
`AlgebraicGeometry.Space.representedSpaceMap_comp`, exactly as for the direct images in
`AlgebraicGeometry.Space.representedModulePushforwardCompIso`. -/
noncomputable abbrev representedModulePullbackCompIso :
    modulePullback B S hS (representedSpaceMap B S hS g) ⋙
        modulePullback B S hS (representedSpaceMap B S hS h) ≅
      modulePullback B S hS (representedSpaceMap B S hS (h ≫ g)) :=
  modulePullbackCompIso B S hS (representedSpaceMap B S hS h)
      (representedSpaceMap B S hS g) ≪≫
    eqToIso (congrArg (modulePullback B S hS) (representedSpaceMap_comp B S hS h g))

/-- The contraction of the two pullbacks along the morphisms of small étale ringed sites of
Stacks 070R (2) of the underlying morphisms of schemes: this is
`AlgebraicGeometry.SmallEtale.smallEtalePullbackCompIso`, the mate of the contraction
`AlgebraicGeometry.Space.representedSchemeModulePushforwardCompIso` of the direct images. -/
noncomputable abbrev representedSchemeModulePullbackCompIso :
    SheafOfModules.pullback.{u} (representedSchemeStructureMapRing B S hS g) ⋙
        SheafOfModules.pullback.{u} (representedSchemeStructureMapRing B S hS h) ≅
      SheafOfModules.pullback.{u} (representedSchemeStructureMapRing B S hS (h ≫ g)) :=
  _root_.AlgebraicGeometry.SmallEtale.smallEtalePullbackCompIso
    (associatedBigEtaleSite B) h.left g.left

/-- **The contraction of the two pullbacks along base change of schemes is conjugate to the
contraction of the two direct images.**  This is
`AlgebraicGeometry.SmallEtale.conjugateEquiv_smallEtalePullbackCompIso_inv` turned round:
that lemma characterises the contraction on its inverse, and this is the characterisation on
its morphism, which is the orientation a composite of conjugates consumes. -/
theorem conjugateEquiv_representedSchemeModulePullbackCompIso :
    conjugateEquiv
        (SheafOfModules.pullbackPushforwardAdjunction.{u}
          (representedSchemeStructureMapRing B S hS (h ≫ g)))
        ((SheafOfModules.pullbackPushforwardAdjunction.{u}
            (representedSchemeStructureMapRing B S hS g)).comp
          (SheafOfModules.pullbackPushforwardAdjunction.{u}
            (representedSchemeStructureMapRing B S hS h)))
        (representedSchemeModulePullbackCompIso B S hS h g).hom =
      (representedSchemeModulePushforwardCompIso B S hS h g).inv :=
  Stacks.CategoryTheory.conjugateEquiv_inv_of_hom _ _
    (representedSchemeModulePullbackCompIso B S hS h g).symm
    (representedSchemeModulePushforwardCompIso B S hS h g)
    (_root_.AlgebraicGeometry.SmallEtale.conjugateEquiv_smallEtalePullbackCompIso_inv
      (associatedBigEtaleSite B) h.left g.left)

/-- **The contraction of the two inverse images of Stacks 03LU is conjugate to the contraction
of the two direct images.**  The contraction is
`AlgebraicGeometry.Space.modulePullbackCompIso` followed by the transport along
`AlgebraicGeometry.Space.representedSpaceMap_comp`; the first factor is
`CategoryTheory.Adjunction.leftAdjointUniq` of the adjunction transported along
`AlgebraicGeometry.Space.modulePushforwardCompIso`, whose conjugate is that isomorphism
inverted, and the conjugate of the transport is the transport of the direct images. -/
theorem conjugateEquiv_representedModulePullbackCompIso :
    conjugateEquiv (modulePullbackAdjunction B S hS (representedSpaceMap B S hS (h ≫ g)))
        ((modulePullbackAdjunction B S hS (representedSpaceMap B S hS g)).comp
          (modulePullbackAdjunction B S hS (representedSpaceMap B S hS h)))
        (representedModulePullbackCompIso B S hS h g).hom =
      (representedModulePushforwardCompIso B S hS h g).inv := by
  have hcomp : conjugateEquiv
        (modulePullbackAdjunction B S hS
          (representedSpaceMap B S hS h ≫ representedSpaceMap B S hS g))
        ((modulePullbackAdjunction B S hS (representedSpaceMap B S hS g)).comp
          (modulePullbackAdjunction B S hS (representedSpaceMap B S hS h)))
        (modulePullbackCompIso B S hS (representedSpaceMap B S hS h)
          (representedSpaceMap B S hS g)).hom =
      (modulePushforwardCompIso B S hS (representedSpaceMap B S hS h)
        (representedSpaceMap B S hS g)).inv :=
    Stacks.CategoryTheory.conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom _ _ _
  rw [show (representedModulePullbackCompIso B S hS h g).hom =
        (modulePullbackCompIso B S hS (representedSpaceMap B S hS h)
            (representedSpaceMap B S hS g)).hom ≫
          eqToHom (congrArg (modulePullback B S hS)
            (representedSpaceMap_comp B S hS h g)) from rfl,
    ← conjugateEquiv_comp _
      (modulePullbackAdjunction B S hS
        (representedSpaceMap B S hS h ≫ representedSpaceMap B S hS g)),
    hcomp, Stacks.CategoryTheory.conjugateEquiv_eqToHom (modulePullback B S hS)
      (modulePushforward B S hS) (modulePullbackAdjunction B S hS)
      (representedSpaceMap_comp B S hS h g)]
  rfl

/-- **The square of inverse images of a representable morphism satisfies the pasting
coherence.**  For `h : T'' ⟶ T'` and `g : T' ⟶ T` of the big fppf category over `S`, pasting the
square of `h` against the square of `g` and contracting the two pullbacks along base change of
schemes is contracting the two inverse images of Stacks 03LU and then taking the square of
`h ≫ g`.

Both sides are isomorphisms of left adjoints, so the coherence is the coherence of their mates,
`AlgebraicGeometry.Space.representedModulePushforwardSquareIso_comp`, read back through
`CategoryTheory.conjugateEquiv` by `Stacks.Mates.pastedSquare_eq_of_conjugate`. -/
theorem representedModulePullbackIso_comp :
    Functor.isoWhiskerLeft (modulePullback B S hS (representedSpaceMap B S hS g))
          (representedModulePullbackIso B S hS h hh) ≪≫
        Functor.isoWhiskerRight (representedModulePullbackIso B S hS g hg)
          (SheafOfModules.pullback.{u} (representedSchemeStructureMapRing B S hS h)) ≪≫
        Functor.isoWhiskerLeft
          ((representedSmallEtaleModuleEquivalence B S hS T).inverse)
          (representedSchemeModulePullbackCompIso B S hS h g) =
      Functor.isoWhiskerRight (representedModulePullbackCompIso B S hS h g)
          ((representedSmallEtaleModuleEquivalence B S hS T'').inverse) ≪≫
        representedModulePullbackIso B S hS (h ≫ g) hhg :=
  Stacks.Mates.pastedSquare_eq_of_conjugate
    (modulePullbackAdjunction B S hS (representedSpaceMap B S hS g))
    (modulePullbackAdjunction B S hS (representedSpaceMap B S hS h))
    (modulePullbackAdjunction B S hS (representedSpaceMap B S hS (h ≫ g)))
    (SheafOfModules.pullbackPushforwardAdjunction.{u}
      (representedSchemeStructureMapRing B S hS g))
    (SheafOfModules.pullbackPushforwardAdjunction.{u}
      (representedSchemeStructureMapRing B S hS h))
    (SheafOfModules.pullbackPushforwardAdjunction.{u}
      (representedSchemeStructureMapRing B S hS (h ≫ g)))
    (representedSmallEtaleModuleEquivalence B S hS T).symm.toAdjunction
    (representedSmallEtaleModuleEquivalence B S hS T').symm.toAdjunction
    (representedSmallEtaleModuleEquivalence B S hS T'').symm.toAdjunction
    (representedModulePullbackIso B S hS g hg) (representedModulePullbackIso B S hS h hh)
    (representedModulePullbackIso B S hS (h ≫ g) hhg)
    (representedModulePullbackCompIso B S hS h g)
    (representedSchemeModulePullbackCompIso B S hS h g)
    (representedModulePushforwardSquareIso B S hS g hg)
    (representedModulePushforwardSquareIso B S hS h hh)
    (representedModulePushforwardSquareIso B S hS (h ≫ g) hhg)
    (representedModulePushforwardCompIso B S hS h g)
    (representedSchemeModulePushforwardCompIso B S hS h g)
    (conjugateEquiv_representedModulePullbackIso_hom B S hS g hg)
    (conjugateEquiv_representedModulePullbackIso_hom B S hS h hh)
    (conjugateEquiv_representedModulePullbackIso_hom B S hS (h ≫ g) hhg)
    (conjugateEquiv_representedModulePullbackCompIso B S hS h g)
    (conjugateEquiv_representedSchemeModulePullbackCompIso B S hS h g)
    (representedModulePushforwardSquareIso_comp B S hS h g hh hg hhg)

end Represented

end AlgebraicGeometry.Space

end
