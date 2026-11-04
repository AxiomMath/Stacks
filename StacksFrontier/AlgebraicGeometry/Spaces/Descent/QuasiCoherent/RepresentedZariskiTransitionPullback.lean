module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.FamilyPullbackComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.RepresentedZariskiTransition

/-!
# The transitions of a descent datum of a represented family under further pullback

`StacksFrontier/AlgebraicGeometry/Spaces/Descent/QuasiCoherent/RepresentedZariskiTransition.lean`
reads the pairwise isomorphisms of a descent datum for quasi-coherent modules relative to a
family of *representable* algebraic spaces on the underlying schemes:
`AlgebraicGeometry.Space.QuasiCoherentDescent.zariskiTransitionOn`, an isomorphism

`r_a^*(F_i|_{Zar}) ≅ r_b^*(F_j|_{Zar})`

for `a : Y ⟶ T i` and `b : Y ⟶ T j` of the big fppf category over `S` agreeing over `U`.  It also
proves that those readings are the identity along one morphism twice and that they compose.

What is still needed to assemble them into a descent datum for
`AlgebraicGeometry.modulePullbackPseudofunctor` relative to the family of underlying morphisms of
schemes is their behaviour under *further pullback*: reading at `(a, b)` and then pulling back
along `h : Y' ⟶ Y` is reading at `(h ≫ a, h ≫ b)`.  This file proves the input that statement is
built from — the same compatibility for the pairwise isomorphism *upstairs*, on the small étale
sites of the representable algebraic spaces, together with the naturality of the comparison
`r^*(F|_{Zar}) ≅ (φ^*F)|_{Zar}` in the module, which is the second half of the computation.

## Main results

* `AlgebraicGeometry.Space.representedModulePullbackCompIso_eq`: the contraction of two inverse
  images along represented morphisms is the contraction of Stacks 03LU at the two represented
  morphisms, with no transport — the composite of two represented morphisms *is* the morphism
  represented by the composite.
* `AlgebraicGeometry.Space.representedZariskiModulePullbackIso_naturality`: **the comparison
  `r^*(F|_{Zar}) ≅ (φ^*F)|_{Zar}` is natural in the module**, and
  `…_naturality_assoc` and `AlgebraicGeometry.Space.representedZariskiModulePullbackIso_comp_assoc`
  are that statement and the composition law of the comparison whiskered with a further
  morphism, which is the shape a transport consumes them in.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.representedSpaceMap_comp_representedPairLift`:
  the morphism into the pairwise fibre product induced by two morphisms agreeing over the target
  is compatible with precomposition.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.transitionOn_representedPairLift_comp`,
  `…_comp'` and `…_comp_hom`: **the pairwise isomorphism of a descent datum read at a pair of
  morphisms of the site, pulled back along a third, is the one read at the composed pair** — as
  an equation of isomorphisms in two arrangements and as an equation of their underlying
  morphisms.
* `…restrictModule_transitionOn_representedPairLift_comp_hom`: the last of these restricted to
  the small Zariski site of the scheme, which is the form in which the transport to the
  underlying schemes consumes it.

## Implementation notes

`AlgebraicGeometry.Space.representedModulePullbackCompIso` is the contraction of Stacks 03LU at
the two represented morphisms followed by a transport along
`AlgebraicGeometry.Space.representedSpaceMap_comp`.  That equality is *definitional* — the
morphism of representable algebraic spaces represented by a composite is the composite of the
represented morphisms on the nose — so the transport is the identity; but `CategoryTheory.eqToIso`
of a proof which is not syntactically `rfl` does not reduce to `CategoryTheory.Iso.refl` at any
affordable cost, and a `rw` that would remove it is refused because its motive is not
type-correct at the `implicit` transparency level.  The transport is therefore cancelled by the
private helper below, applied as a term: at an *abstract* object there is nothing to unfold.

The compatibility is proved as an equation of isomorphisms first, in the arrangement
`AlgebraicGeometry.Space.QuasiCoherentDescent.transitionOn_comp` delivers it in — comparison,
transition, inverse comparison — and only then rearranged and read on the underlying morphisms.
Going the other way round is measurably worse: the two comparisons that have to cancel are then
produced by two different rewrites, and `CategoryTheory.Iso.symm_self_id` does not see them as one
isomorphism.

No `stacks` attribute is registered.  Stacks 04W3 is tagged where
`AlgebraicGeometry.Space.QuasiCoherentDescent.DescentDatum` is defined and Stacks 03LU where
`AlgebraicGeometry.Space.modulePullback` is built; what is added here is a step in the transport
of a descent datum of a represented family to the underlying schemes, which is a step in the
proof of Stacks 04W8.

## References

* [Stacks Project, Tag 04W3](https://stacks.math.columbia.edu/tag/04W3)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 023B](https://stacks.math.columbia.edu/tag/023B)
* [Stacks Project, Tag 04W8](https://stacks.math.columbia.edu/tag/04W8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Transport

variable {C₀ : Type*} [Category C₀]

/-- A transport along an equality of an object with itself cancels.  Stated at an abstract
object, where the proof can be replaced by `rfl` without unfolding anything. -/
private theorem trans_eqToIso_of_eq_self {X Y : C₀} (e : X ≅ Y) (p : Y = Y) :
    e ≪≫ eqToIso p = e := by
  obtain rfl : p = rfl := rfl
  simp

end Transport

/-- **The contraction of two inverse images along represented morphisms is the contraction of
Stacks 03LU at the two represented morphisms.**  The morphism of representable algebraic spaces
represented by a composite of the big fppf category over `S` is the composite of the represented
morphisms definitionally, so the transport in
`AlgebraicGeometry.Space.representedModulePullbackCompIso` contributes nothing. -/
public theorem representedModulePullbackCompIso_eq {T'' T' T : BigFppfOver B S hS}
    (h : T'' ⟶ T') (g : T' ⟶ T) :
    representedModulePullbackCompIso B S hS h g =
      modulePullbackCompIso B S hS (representedSpaceMap B S hS h)
        (representedSpaceMap B S hS g) :=
  trans_eqToIso_of_eq_self
    (modulePullbackCompIso B S hS (representedSpaceMap B S hS h)
      (representedSpaceMap B S hS g))
    (congrArg (modulePullback B S hS) (representedSpaceMap_comp B S hS h g))

section Naturality

variable {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
  (hg : yoneda.relativelyRepresentable (yoneda.map g))

/-- **The comparison `r^*(F|_{T_Zar}) ≅ (φ^*F)|_{T'_Zar}` is natural in the module.**  For a
morphism `ψ : F ⟶ F'` of quasi-coherent `𝒪`-modules on the small étale site of the representable
algebraic space `yoneda.obj T`, the comparison intertwines the restriction of `ψ` pulled back
along the underlying morphism of schemes with the restriction of its inverse image of
Stacks 03LU.

The two factors of the comparison contribute their own naturality:
`AlgebraicGeometry.SmallEtale.restrictModulePullbackObjIso_naturality` for the restriction to the
small Zariski site and the naturality of the square
`AlgebraicGeometry.Space.representedModulePullbackIso` for the identification of the small étale
sites, the second solved for its inverse arrows, which is the orientation the comparison reads
them in. -/
public theorem representedZariskiModulePullbackIso_naturality
    {F F' : SheafOfModules.{u} (representedStructureRingSheaf B S hS T)}
    (hF : F.IsQuasicoherentOnSite) (hF' : F'.IsQuasicoherentOnSite) (ψ : F ⟶ F') :
    (Scheme.Modules.pullback
            (_root_.AlgebraicGeometry.SmallEtale.schemeHom
              (associatedBigEtaleSite B) g.left)).map
          ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj T) T.left.property).map
            ((representedSmallEtaleModuleEquivalence B S hS T).inverse.map ψ)) ≫
        (representedZariskiModulePullbackIso B S hS g hg F' hF').hom =
      (representedZariskiModulePullbackIso B S hS g hg F hF).hom ≫
        (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj T') T'.left.property).map
          ((representedSmallEtaleModuleEquivalence B S hS T').inverse.map
            ((modulePullback B S hS (representedSpaceMap B S hS g)).map ψ)) := by
  have nat1 : (Scheme.Modules.pullback
            (_root_.AlgebraicGeometry.SmallEtale.schemeHom
              (associatedBigEtaleSite B) g.left)).map
          ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj T) T.left.property).map
            ((representedSmallEtaleModuleEquivalence B S hS T).inverse.map ψ)) ≫
        (_root_.AlgebraicGeometry.SmallEtale.restrictModulePullbackObjIso
          (associatedBigEtaleSite B) g.left
          ((representedSmallEtaleModuleEquivalence B S hS T).inverse.obj F')
          (isQuasicoherentOnSite_representedSmallEtaleInverse B S hS T F' hF')).hom =
      (_root_.AlgebraicGeometry.SmallEtale.restrictModulePullbackObjIso
          (associatedBigEtaleSite B) g.left
          ((representedSmallEtaleModuleEquivalence B S hS T).inverse.obj F)
          (isQuasicoherentOnSite_representedSmallEtaleInverse B S hS T F hF)).hom ≫
        (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj T') T'.left.property).map
          ((SheafOfModules.pullback.{u} (representedSchemeStructureMapRing B S hS g)).map
            ((representedSmallEtaleModuleEquivalence B S hS T).inverse.map ψ)) :=
    _root_.AlgebraicGeometry.SmallEtale.restrictModulePullbackObjIso_naturality
      (associatedBigEtaleSite B) g.left
      (isQuasicoherentOnSite_representedSmallEtaleInverse B S hS T F hF)
      (isQuasicoherentOnSite_representedSmallEtaleInverse B S hS T F' hF') _
  have nat2 : (representedSmallEtaleModuleEquivalence B S hS T').inverse.map
          ((modulePullback B S hS (representedSpaceMap B S hS g)).map ψ) ≫
        ((representedModulePullbackIso B S hS g hg).app F').hom =
      ((representedModulePullbackIso B S hS g hg).app F).hom ≫
        (SheafOfModules.pullback.{u} (representedSchemeStructureMapRing B S hS g)).map
          ((representedSmallEtaleModuleEquivalence B S hS T).inverse.map ψ) :=
    (representedModulePullbackIso B S hS g hg).hom.naturality ψ
  have key : (SheafOfModules.pullback.{u} (representedSchemeStructureMapRing B S hS g)).map
          ((representedSmallEtaleModuleEquivalence B S hS T).inverse.map ψ) ≫
        ((representedModulePullbackIso B S hS g hg).app F').inv =
      ((representedModulePullbackIso B S hS g hg).app F).inv ≫
        (representedSmallEtaleModuleEquivalence B S hS T').inverse.map
          ((modulePullback B S hS (representedSpaceMap B S hS g)).map ψ) := by
    rw [Iso.comp_inv_eq, Category.assoc, nat2, Iso.inv_hom_id_assoc]
  have key2 := congrArg (_root_.AlgebraicGeometry.SmallEtale.restrictModule
    (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj T') T'.left.property).map key
  simp only [Functor.map_comp] at key2
  rw [representedZariskiModulePullbackIso_hom, representedZariskiModulePullbackIso_hom,
    ← Category.assoc, nat1, Category.assoc, key2]
  exact (Category.assoc _ _ _).symm

/-- `AlgebraicGeometry.Space.representedZariskiModulePullbackIso_naturality`, whiskered with a
further morphism, which is the shape a transport consumes it in. -/
public theorem representedZariskiModulePullbackIso_naturality_assoc
    {F F' : SheafOfModules.{u} (representedStructureRingSheaf B S hS T)}
    (hF : F.IsQuasicoherentOnSite) (hF' : F'.IsQuasicoherentOnSite) (ψ : F ⟶ F')
    {Q : ((BigFppfOver.toScheme B S hS).obj T').Modules}
    (k : representedZariskiModule B S hS T'
      ((modulePullback B S hS (representedSpaceMap B S hS g)).obj F') ⟶ Q) :
    (Scheme.Modules.pullback
            (_root_.AlgebraicGeometry.SmallEtale.schemeHom
              (associatedBigEtaleSite B) g.left)).map
          ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj T) T.left.property).map
            ((representedSmallEtaleModuleEquivalence B S hS T).inverse.map ψ)) ≫
        (representedZariskiModulePullbackIso B S hS g hg F' hF').hom ≫ k =
      (representedZariskiModulePullbackIso B S hS g hg F hF).hom ≫
        (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj T') T'.left.property).map
          ((representedSmallEtaleModuleEquivalence B S hS T').inverse.map
            ((modulePullback B S hS (representedSpaceMap B S hS g)).map ψ)) ≫ k := by
  exact (reassoc_of% (representedZariskiModulePullbackIso_naturality B S hS g hg hF hF' ψ)) k

end Naturality

section CompAssoc

variable {T'' T' T : BigFppfOver B S hS} (h : T'' ⟶ T') (g : T' ⟶ T)
  (hh : yoneda.relativelyRepresentable (yoneda.map h))
  (hg : yoneda.relativelyRepresentable (yoneda.map g))
  (hhg : yoneda.relativelyRepresentable (yoneda.map (h ≫ g)))

/-- `AlgebraicGeometry.Space.representedZariskiModulePullbackIso_comp`, whiskered with a further
morphism, which is the shape a transport consumes it in. -/
public theorem representedZariskiModulePullbackIso_comp_assoc
    (F : SheafOfModules.{u} (representedStructureRingSheaf B S hS T))
    (hF : F.IsQuasicoherentOnSite)
    {Q : ((BigFppfOver.toScheme B S hS).obj T'').Modules}
    (k : representedZariskiModule B S hS T''
      ((modulePullback B S hS (representedSpaceMap B S hS (h ≫ g))).obj F) ⟶ Q) :
    (Scheme.Modules.pullback
            (_root_.AlgebraicGeometry.SmallEtale.schemeHom
              (associatedBigEtaleSite B) h.left)).map
          (representedZariskiModulePullbackIso B S hS g hg F hF).hom ≫
        (representedZariskiModulePullbackIso B S hS h hh
          ((modulePullback B S hS (representedSpaceMap B S hS g)).obj F)
          (isQuasicoherentOnSite_modulePullback_representedSpaceMap B S hS g hg F hF)).hom ≫
        (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj T'') T''.left.property).map
          ((representedSmallEtaleModuleEquivalence B S hS T'').inverse.map
            ((representedModulePullbackCompIso B S hS h g).hom.app F)) ≫ k =
      (Scheme.Modules.pullbackComp
            (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) h.left)
            (_root_.AlgebraicGeometry.SmallEtale.schemeHom
              (associatedBigEtaleSite B) g.left)).hom.app
          (representedZariskiModule B S hS T F) ≫
        (representedZariskiModulePullbackIso B S hS (h ≫ g) hhg F hF).hom ≫ k := by
  simpa using (reassoc_of% (representedZariskiModulePullbackIso_comp B S hS h g hh hg hhg F hF)) k

end CompAssoc

namespace QuasiCoherentDescent

section Represented

variable {I : Type v} {U : BigFppfOver B S hS} (T : I → BigFppfOver B S hS)
  (f : ∀ i, T i ⟶ U)

/-- **The morphism into a pairwise fibre product induced by two morphisms agreeing over the
target is compatible with precomposition.**  Both sides are lifts of the same pair of morphisms
through the same fibre product, so they agree by its universal property. -/
public theorem representedSpaceMap_comp_representedPairLift {Y Y' : BigFppfOver B S hS}
    (h : Y' ⟶ Y) {q : Y ⟶ U} {i j : I} (a : Y ⟶ T i) (b : Y ⟶ T j) (ha : a ≫ f i = q)
    (hb : b ≫ f j = q) {q' : Y' ⟶ U} (ha' : (h ≫ a) ≫ f i = q')
    (hb' : (h ≫ b) ≫ f j = q') :
    representedSpaceMap B S hS h ≫ representedPairLift B S hS T f a b ha hb =
      representedPairLift B S hS T f (h ≫ a) (h ≫ b) ha' hb' := by
  refine (AlgebraicSpaces.isPullback_fiberProduct B S hS
    (representedFamilyMap B S hS T f i) (representedFamilyMap B S hS T f j)).hom_ext ?_ ?_
  · rw [Category.assoc, representedPairLift_fst, representedPairLift_fst]
    exact representedSpaceMap_comp B S hS h a
  · rw [Category.assoc, representedPairLift_snd, representedPairLift_snd]
    exact representedSpaceMap_comp B S hS h b

variable (D : DescentDatum B S hS (representedFamily B S hS T) (representedFamilyMap B S hS T f))
variable {Y Y' : BigFppfOver B S hS} (h : Y' ⟶ Y) {q : Y ⟶ U} {i j : I}
  (a : Y ⟶ T i) (b : Y ⟶ T j) (ha : a ≫ f i = q) (hb : b ≫ f j = q)
  {q' : Y' ⟶ U} (ha' : (h ≫ a) ≫ f i = q') (hb' : (h ≫ b) ≫ f j = q')

/-- **The pairwise isomorphism of a descent datum of a represented family, read at a pair of
morphisms of the site and pulled back along a third, is the one read at the composed pair.**

This is `AlgebraicGeometry.Space.QuasiCoherentDescent.transitionOn_comp` — the reading of a
pairwise isomorphism on a test space is compatible with pullback — at the test space
`yoneda.obj Y` and the morphism represented by `h`, with the induced morphism into the pairwise
fibre product identified by
`AlgebraicGeometry.Space.QuasiCoherentDescent.representedSpaceMap_comp_representedPairLift` and
the contractions of the iterated inverse images written as
`AlgebraicGeometry.Space.representedModulePullbackCompIso`. -/
public theorem transitionOn_representedPairLift_comp :
    (modulePullback B S hS (representedSpaceMap B S hS h)).mapIso
        (transitionOn B S hS (representedFamily B S hS T) (representedFamilyMap B S hS T f)
          D.F D.transition i j (representedPairLift B S hS T f a b ha hb)
          (representedSpaceMap B S hS a) (representedSpaceMap B S hS b)
          (representedPairLift_fst B S hS T f a b ha hb)
          (representedPairLift_snd B S hS T f a b ha hb)) =
      (representedModulePullbackCompIso B S hS h a).app (D.F i) ≪≫
        transitionOn B S hS (representedFamily B S hS T) (representedFamilyMap B S hS T f)
          D.F D.transition i j (representedPairLift B S hS T f (h ≫ a) (h ≫ b) ha' hb')
          (representedSpaceMap B S hS (h ≫ a)) (representedSpaceMap B S hS (h ≫ b))
          (representedPairLift_fst B S hS T f (h ≫ a) (h ≫ b) ha' hb')
          (representedPairLift_snd B S hS T f (h ≫ a) (h ≫ b) ha' hb') ≪≫
        ((representedModulePullbackCompIso B S hS h b).app (D.F j)).symm := by
  have hT := transitionOn_congr_map B S hS (representedFamily B S hS T)
    (representedFamilyMap B S hS T f) D.F D.transition i j
    (representedSpaceMap_comp_representedPairLift B S hS T f h a b ha hb ha' hb')
    (representedSpaceMap B S hS (h ≫ a)) (representedSpaceMap B S hS (h ≫ b))
    (by rw [Category.assoc, representedPairLift_fst]
        exact representedSpaceMap_comp B S hS h a)
    (by rw [Category.assoc, representedPairLift_snd]
        exact representedSpaceMap_comp B S hS h b)
    (representedPairLift_fst B S hS T f (h ≫ a) (h ≫ b) ha' hb')
    (representedPairLift_snd B S hS T f (h ≫ a) (h ≫ b) ha' hb')
  rw [representedModulePullbackCompIso_eq, representedModulePullbackCompIso_eq,
    transitionOn_comp B S hS
      (representedFamily B S hS T) (representedFamilyMap B S hS T f) D.F D.transition
      (representedSpaceMap B S hS h) i j (representedPairLift B S hS T f a b ha hb)
      (representedSpaceMap B S hS a) (representedSpaceMap B S hS b)
      (representedPairLift_fst B S hS T f a b ha hb)
      (representedPairLift_snd B S hS T f a b ha hb)]
  exact congrArg (fun z => (modulePullbackCompIso B S hS (representedSpaceMap B S hS h)
      (representedSpaceMap B S hS a)).app (D.F i) ≪≫ z ≪≫
    ((modulePullbackCompIso B S hS (representedSpaceMap B S hS h)
      (representedSpaceMap B S hS b)).app (D.F j)).symm) hT

/-- `AlgebraicGeometry.Space.QuasiCoherentDescent.transitionOn_representedPairLift_comp` with the
contraction below `b` moved to the other side, which is the arrangement a transport reads. -/
public theorem transitionOn_representedPairLift_comp' :
    (modulePullback B S hS (representedSpaceMap B S hS h)).mapIso
          (transitionOn B S hS (representedFamily B S hS T) (representedFamilyMap B S hS T f)
            D.F D.transition i j (representedPairLift B S hS T f a b ha hb)
            (representedSpaceMap B S hS a) (representedSpaceMap B S hS b)
            (representedPairLift_fst B S hS T f a b ha hb)
            (representedPairLift_snd B S hS T f a b ha hb)) ≪≫
        (representedModulePullbackCompIso B S hS h b).app (D.F j) =
      (representedModulePullbackCompIso B S hS h a).app (D.F i) ≪≫
        transitionOn B S hS (representedFamily B S hS T) (representedFamilyMap B S hS T f)
          D.F D.transition i j (representedPairLift B S hS T f (h ≫ a) (h ≫ b) ha' hb')
          (representedSpaceMap B S hS (h ≫ a)) (representedSpaceMap B S hS (h ≫ b))
          (representedPairLift_fst B S hS T f (h ≫ a) (h ≫ b) ha' hb')
          (representedPairLift_snd B S hS T f (h ≫ a) (h ≫ b) ha' hb') := by
  rw [transitionOn_representedPairLift_comp B S hS T f D h a b ha hb ha' hb',
    Iso.trans_assoc, Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl]

/-- `AlgebraicGeometry.Space.QuasiCoherentDescent.transitionOn_representedPairLift_comp'`, read
on the underlying morphisms, so that a consumer rewrites rather than distributing the
isomorphisms itself. -/
public theorem transitionOn_representedPairLift_comp_hom :
    (modulePullback B S hS (representedSpaceMap B S hS h)).map
          (transitionOn B S hS (representedFamily B S hS T) (representedFamilyMap B S hS T f)
            D.F D.transition i j (representedPairLift B S hS T f a b ha hb)
            (representedSpaceMap B S hS a) (representedSpaceMap B S hS b)
            (representedPairLift_fst B S hS T f a b ha hb)
            (representedPairLift_snd B S hS T f a b ha hb)).hom ≫
        (representedModulePullbackCompIso B S hS h b).hom.app (D.F j) =
      (representedModulePullbackCompIso B S hS h a).hom.app (D.F i) ≫
        (transitionOn B S hS (representedFamily B S hS T) (representedFamilyMap B S hS T f)
          D.F D.transition i j (representedPairLift B S hS T f (h ≫ a) (h ≫ b) ha' hb')
          (representedSpaceMap B S hS (h ≫ a)) (representedSpaceMap B S hS (h ≫ b))
          (representedPairLift_fst B S hS T f (h ≫ a) (h ≫ b) ha' hb')
          (representedPairLift_snd B S hS T f (h ≫ a) (h ≫ b) ha' hb')).hom := by
  have key := congrArg Iso.hom
    (transitionOn_representedPairLift_comp' B S hS T f D h a b ha hb ha' hb')
  simpa only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom] using key

section Coherence

attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite

/-- `AlgebraicGeometry.Space.QuasiCoherentDescent.transitionOn_representedPairLift_comp_hom`,
restricted to the small Zariski site of the scheme underlying `Y'`.

Composition in the category of `𝒪`-modules of an algebraic space is a projection of
`AlgebraicGeometry.Space.smallEtaleRingedSite`, so a `rw` with
`CategoryTheory.Functor.map_comp` does not see the composite that has to be distributed; that one
definition is made locally `implicit_reducible`, and nothing else is relaxed. -/
public theorem restrictModule_transitionOn_representedPairLift_comp_hom :
    (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj Y') Y'.left.property).map
        ((representedSmallEtaleModuleEquivalence B S hS Y').inverse.map
          ((modulePullback B S hS (representedSpaceMap B S hS h)).map
            (transitionOn B S hS (representedFamily B S hS T)
            (representedFamilyMap B S hS T f) D.F D.transition i j
            (representedPairLift B S hS T f a b ha hb)
            (representedSpaceMap B S hS a) (representedSpaceMap B S hS b)
            (representedPairLift_fst B S hS T f a b ha hb)
            (representedPairLift_snd B S hS T f a b ha hb)).hom)) ≫
        (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj Y') Y'.left.property).map
        ((representedSmallEtaleModuleEquivalence B S hS Y').inverse.map
          ((representedModulePullbackCompIso B S hS h b).hom.app (D.F j))) =
      (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj Y') Y'.left.property).map
        ((representedSmallEtaleModuleEquivalence B S hS Y').inverse.map
          ((representedModulePullbackCompIso B S hS h a).hom.app (D.F i))) ≫
        (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj Y') Y'.left.property).map
        ((representedSmallEtaleModuleEquivalence B S hS Y').inverse.map
          (transitionOn B S hS (representedFamily B S hS T)
            (representedFamilyMap B S hS T f) D.F D.transition i j
            (representedPairLift B S hS T f (h ≫ a) (h ≫ b) ha' hb')
            (representedSpaceMap B S hS (h ≫ a)) (representedSpaceMap B S hS (h ≫ b))
            (representedPairLift_fst B S hS T f (h ≫ a) (h ≫ b) ha' hb')
            (representedPairLift_snd B S hS T f (h ≫ a) (h ≫ b) ha' hb')).hom) := by
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp,
    transitionOn_representedPairLift_comp_hom B S hS T f D h a b ha hb ha' hb']

end Coherence

end Represented

end QuasiCoherentDescent

end AlgebraicGeometry.Space

end
