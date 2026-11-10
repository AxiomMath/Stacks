module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.CanonicalDatum
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.RepresentedZariskiTransitionSquare

/-!
# The canonical descent datum of a represented family, read on the underlying schemes

Let `f i : T i ⟶ U` be a family of the big fppf category over a scheme `S` and let `N` be a
quasi-coherent `𝒪`-module on the representable algebraic space `yoneda.obj U`.  The canonical
descent datum of Stacks 04W5 of `N`, relative to the family of representable algebraic spaces the
family represents, has for its pairwise isomorphism the canonical comparison of the two inverse
images.  **This file reads that datum on the underlying schemes**: its reading
`AlgebraicGeometry.Space.QuasiCoherentDescent.zariskiTransitionOn` is the canonical comparison of
the two iterated pullbacks of the module of `N` on the scheme underlying `U`, conjugated by the
comparison `AlgebraicGeometry.Space.representedZariskiModulePullbackIso` on either side.

That is the one half of the pairwise condition of step 1 of the effectivity clause of Stacks 04W8
that the scheme side does not supply: the other half, the reading of the given datum, is
`AlgebraicGeometry.Space.QuasiCoherentDescent.reprSchemeDatum_hom`, which is
`zariskiTransitionOn` on the nose.

## Main results

* `AlgebraicGeometry.Space.QuasiCoherentDescent.canonicalComparison_representedSpaceMap`: the
  canonical comparison of the two inverse images along two represented morphisms, written through
  the contraction `AlgebraicGeometry.Space.representedModulePullbackCompIso` of two inverse images
  and a transport along the equality of the two composites **in the site**.
* `AlgebraicGeometry.Space.representedZariskiModulePullbackIso_congr`: the comparison
  `AlgebraicGeometry.Space.representedZariskiModulePullbackIso` at two equal morphisms of the
  site, the two transports on either side.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.zariskiTransitionOn_canonicalDescentDatum`:
  **the reading of the canonical descent datum of `N` is the canonical comparison on the
  underlying schemes.**

## Implementation notes

Every statement here carries the equality of morphisms it transports along **as a hypothesis**,
rather than letting the elaborator find it: the morphism of schemes underlying a composite of the
site and the composite of the two underlying morphisms are the same term, as are the two
corresponding morphisms of algebraic spaces, but asking for that identification in the middle of
a chain of `≪≫` is a deterministic timeout at `whnf`, while the same identification asked
for at one object — `(Scheme.Modules.pullback (f ≫ g)).obj M` against
`(Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback g).obj M` — costs nothing.  So the two
spellings are kept apart by hypotheses, and no statement here mixes them.

That is also why `…canonicalComparison_representedSpaceMap` exists.  Expanding the canonical
comparison with the general `AlgebraicGeometry.Space.QuasiCoherentDescent.canonicalComparison_eq`
produces a transport along the equality of the two composites *of represented morphisms*, whereas
the contraction of two inverse images along represented morphisms is stated at the morphism
represented by the composite; the two then meet underneath `≪≫` and the final comparison exhausts
the elaborator in every form, `convert … using 1`, `using 2` and `using 4` included.  Expanding
in the second spelling from the start removes the meeting altogether and the final step is an
`exact`.

The pasting `Stacks.iso_paste_pair` is stated at a variable category, so that the two
cancellations it performs are never asked for at the modules of a representable algebraic space.

No `stacks` attribute is registered: Stacks 04W5 is tagged where the canonical descent datum is
defined and Stacks 03LU where the comparison of iterated inverse images is, and what is added
here is the dictionary between the two sides of step 1 of the proof of Stacks 04W8.

## References

* [Stacks Project, Tag 04W8](https://stacks.math.columbia.edu/tag/04W8)
* [Stacks Project, Tag 04W5](https://stacks.math.columbia.edu/tag/04W5)
* [Stacks Project, Tag 04W3](https://stacks.math.columbia.edu/tag/04W3)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace Stacks

section Paste

variable {C₀ : Type*} [Category C₀]

/-- **The pasting of two commuting squares of isomorphisms joined by a third.**  The two squares
`h1` and `h2` identify a three-fold composite with a two-fold one on either side, and `h3`
connects the two short sides; the conclusion runs the long way round.

Stated at abstract objects of an abstract category, which is where the cancellations are
affordable: instantiated at the modules of a representable algebraic space, the same two
cancellations ask the kernel to reduce a composition of morphisms of modules. -/
public theorem iso_paste_pair {A A1 A2 A3 A4 B2 B1 B0 Ca Cb : C₀}
    (Ma : A ≅ A1) (Pa : A1 ≅ A2) (Ra : A2 ≅ A3) (Req : A3 ≅ A4)
    (Rb : B2 ≅ A4) (Pb : B1 ≅ B2) (Mb : B0 ≅ B1)
    (Ka : A ≅ Ca) (Qa : Ca ≅ A3) (Kb : B0 ≅ Cb) (Qb : Cb ≅ A4) (Eqi : Ca ≅ Cb)
    (h1 : Ma ≪≫ Pa ≪≫ Ra = Ka ≪≫ Qa)
    (h2 : Mb ≪≫ Pb ≪≫ Rb = Kb ≪≫ Qb)
    (h3 : Qa ≪≫ Req = Eqi ≪≫ Qb) :
    Ma ≪≫ Pa ≪≫ Ra ≪≫ Req ≪≫ Rb.symm ≪≫ Pb.symm = Ka ≪≫ Eqi ≪≫ Kb.symm ≪≫ Mb := by
  refine Iso.ext ?_
  have e1 := congrArg Iso.hom h1
  have e2 := congrArg Iso.hom h2
  have e3 := congrArg Iso.hom h3
  simp only [Iso.trans_hom, Iso.symm_hom] at e1 e2 e3 ⊢
  rw [reassoc_of% e1, reassoc_of% e3, (Iso.eq_inv_comp Kb).mpr e2.symm]
  simp

end Paste

end Stacks

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Congr

attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite

/-- **The comparison `AlgebraicGeometry.Space.representedZariskiModulePullbackIso` at two equal
morphisms of the site, with the transport along that equality on either side.**

The equality is of morphisms of the site, and both transports are built from it, so that a
consumer never has to identify the morphism of schemes underlying a composite with the composite
of the underlying morphisms. -/
public theorem representedZariskiModulePullbackIso_congr {V W : BigFppfOver B S hS}
    {g g' : V ⟶ W} (F : SheafOfModules.{u} (representedStructureRingSheaf B S hS W))
    (hF : F.IsQuasicoherentOnSite) (h : g = g') :
    representedZariskiModulePullbackIso B S hS g
          (relativelyRepresentable_yoneda_map B S hS g) F hF ≪≫
        (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj V) V.left.property).mapIso
          ((representedSmallEtaleModuleEquivalence B S hS V).inverse.mapIso
            (eqToIso (congrArg (fun m : V ⟶ W =>
              (modulePullback B S hS (representedSpaceMap B S hS m)).obj F) h))) =
      eqToIso (congrArg (fun m : V ⟶ W => (Scheme.Modules.pullback
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom
            (associatedBigEtaleSite B) m.left)).obj
            (representedZariskiModule B S hS W F)) h) ≪≫
        representedZariskiModulePullbackIso B S hS g'
          (relativelyRepresentable_yoneda_map B S hS g') F hF := by
  subst h
  simp only [eqToIso_refl, Functor.mapIso_refl, Iso.trans_refl, Iso.refl_trans]

end Congr

namespace QuasiCoherentDescent

section Comparison

attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite

/-- **The canonical comparison of the two inverse images of a module along two represented
morphisms with equal composites in the site.**  It is the contraction of two inverse images below
the first pair, a transport along the equality of the two composites **in the site**, and the
inverse of the contraction below the second pair.

This is `AlgebraicGeometry.Space.QuasiCoherentDescent.canonicalComparison_eq` with both
contractions taken at the represented morphisms, by
`AlgebraicGeometry.Space.representedModulePullbackCompIso_eq`, and the transport restated along
the equality of the two composites of the site.  Stating it this way is what makes the reading of
the canonical descent datum below affordable: the general form transports along the equality of
the two composites of *represented* morphisms, which is a second spelling of the same object, and
the two spellings then meet underneath `≪≫`. -/
public theorem canonicalComparison_representedSpaceMap {V W₁ W₂ W : BigFppfOver B S hS}
    (a : V ⟶ W₁) (b : V ⟶ W₂) (p : W₁ ⟶ W) (r : W₂ ⟶ W) (hab : a ≫ p = b ≫ r)
    (hc : representedSpaceMap B S hS a ≫ representedSpaceMap B S hS p =
      representedSpaceMap B S hS b ≫ representedSpaceMap B S hS r)
    (N : SheafOfModules.{u} (representedStructureRingSheaf B S hS W)) :
    canonicalComparison (representedSpaceMap B S hS a) (representedSpaceMap B S hS b)
        (representedSpaceMap B S hS p) (representedSpaceMap B S hS r) hc N =
      (representedModulePullbackCompIso B S hS a p).app N ≪≫
        eqToIso (congrArg (fun m : V ⟶ W =>
          (modulePullback B S hS (representedSpaceMap B S hS m)).obj N) hab) ≪≫
        ((representedModulePullbackCompIso B S hS b r).app N).symm := by
  rw [canonicalComparison_eq, representedModulePullbackCompIso_eq,
    representedModulePullbackCompIso_eq]
  rfl

end Comparison

section Represented

variable {I : Type v} {U : BigFppfOver B S hS} (T : I → BigFppfOver B S hS)
  (f : ∀ i, T i ⟶ U)

attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite

/-- `AlgebraicGeometry.Space.QuasiCoherentDescent.zariskiTransitionOn` written out as an equality
of isomorphisms, which is the form in which a composition of such laws is affordable;
`AlgebraicGeometry.Space.QuasiCoherentDescent.zariskiTransitionOn_hom` is the same equation
between the underlying morphisms. -/
public theorem zariskiTransitionOn_eq
    (D : DescentDatum B S hS (representedFamily B S hS T) (representedFamilyMap B S hS T f))
    {Y : BigFppfOver B S hS} {q : Y ⟶ U} {i j : I}
    (a : Y ⟶ T i) (b : Y ⟶ T j) (ha : a ≫ f i = q) (hb : b ≫ f j = q) :
    zariskiTransitionOn B S hS T f D a b ha hb =
      representedZariskiModulePullbackIso B S hS a
          (relativelyRepresentable_yoneda_map B S hS a) (D.F i) (D.quasicoherent i) ≪≫
        (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj Y) Y.left.property).mapIso
          ((representedSmallEtaleModuleEquivalence B S hS Y).inverse.mapIso
            (transitionOn B S hS (representedFamily B S hS T)
              (representedFamilyMap B S hS T f) D.F D.transition i j
              (representedPairLift B S hS T f a b ha hb)
              (representedSpaceMap B S hS a) (representedSpaceMap B S hS b)
              (representedPairLift_fst B S hS T f a b ha hb)
              (representedPairLift_snd B S hS T f a b ha hb))) ≪≫
        (representedZariskiModulePullbackIso B S hS b
          (relativelyRepresentable_yoneda_map B S hS b) (D.F j) (D.quasicoherent j)).symm :=
  rfl

/-- **The reading of the canonical descent datum of Stacks 04W5 on the underlying schemes is the
canonical comparison there.**  For a quasi-coherent `𝒪`-module `N` on `yoneda.obj U`, the pairwise
isomorphism of the canonical descent datum of `N` relative to the represented family, read at two
morphisms `a`, `b` of the site agreeing over `U`, is — once the components are identified with the
pullbacks of the module of `N` on the scheme underlying `U` by
`AlgebraicGeometry.Space.representedZariskiModulePullbackIso` — the comparison of the two
iterated pullbacks of that module through the pullback of the common composite.

The equality `hsh` of the two composites of morphisms of schemes is a hypothesis: it is provable,
but the two spellings of that composite must not meet inside the statement. -/
public theorem zariskiTransitionOn_canonicalDescentDatum
    (N : SheafOfModules.{u} (representedStructureRingSheaf B S hS U))
    (hN : N.IsQuasicoherentOnSite)
    {Y : BigFppfOver B S hS} {q : Y ⟶ U} {i j : I}
    (a : Y ⟶ T i) (b : Y ⟶ T j) (ha : a ≫ f i = q) (hb : b ≫ f j = q)
    (hsh : _root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) a.left ≫
        _root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) (f i).left =
      _root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) b.left ≫
        _root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) (f j).left) :
    (Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
          (associatedBigEtaleSite B) a.left)).mapIso
        (representedZariskiModulePullbackIso B S hS (f i)
          (relativelyRepresentable_yoneda_map B S hS (f i)) N hN) ≪≫
      zariskiTransitionOn B S hS T f
        (canonicalDescentDatum B S hS (representedFamily B S hS T)
          (representedFamilyMap B S hS T f) N hN) a b ha hb =
    (Scheme.Modules.pullbackComp
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) a.left)
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom
            (associatedBigEtaleSite B) (f i).left)).app
        (representedZariskiModule B S hS U N) ≪≫
      eqToIso (congrArg (fun m => (Scheme.Modules.pullback m).obj
          (representedZariskiModule B S hS U N)) hsh) ≪≫
      ((Scheme.Modules.pullbackComp
            (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) b.left)
            (_root_.AlgebraicGeometry.SmallEtale.schemeHom
              (associatedBigEtaleSite B) (f j).left)).app
          (representedZariskiModule B S hS U N)).symm ≪≫
      (Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
            (associatedBigEtaleSite B) b.left)).mapIso
        (representedZariskiModulePullbackIso B S hS (f j)
          (relativelyRepresentable_yoneda_map B S hS (f j)) N hN) := by
  have hinner := transitionOn_canonicalComparison B S hS (representedFamily B S hS T)
    (representedFamilyMap B S hS T f) N i j (representedPairLift B S hS T f a b ha hb)
    (representedSpaceMap B S hS a) (representedSpaceMap B S hS b)
    (representedPairLift_fst B S hS T f a b ha hb)
    (representedPairLift_snd B S hS T f a b ha hb)
  rw [zariskiTransitionOn_eq]
  simp only [canonicalDescentDatum]
  rw [hinner, canonicalComparison_representedSpaceMap B S hS a b (f i) (f j)
    (ha.trans hb.symm) _ N]
  simp only [representedFamilyMap, Functor.mapIso_trans, Functor.mapIso_symm,
    Iso.trans_assoc]
  exact Stacks.iso_paste_pair _ _ _ _ _ _ _ _ _ _ _ _
    (representedZariskiModulePullbackIso_comp_iso B S hS a (f i)
      (relativelyRepresentable_yoneda_map B S hS a)
      (relativelyRepresentable_yoneda_map B S hS (f i))
      (relativelyRepresentable_yoneda_map B S hS (a ≫ f i)) N hN)
    (representedZariskiModulePullbackIso_comp_iso B S hS b (f j)
      (relativelyRepresentable_yoneda_map B S hS b)
      (relativelyRepresentable_yoneda_map B S hS (f j))
      (relativelyRepresentable_yoneda_map B S hS (b ≫ f j)) N hN)
    (representedZariskiModulePullbackIso_congr B S hS N hN (ha.trans hb.symm))

end Represented

end QuasiCoherentDescent

end AlgebraicGeometry.Space

end
