module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.RefinementFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedFamilyChosenPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiModulePullback

/-!
# The transitions of a descent datum of a represented family, read on the underlying schemes

Let `f i : T i ⟶ U` be a family of the big fppf category over `S`.  Its members and its target
represent algebraic spaces over `S`, so a descent datum for quasi-coherent modules of
**Stacks 04W3** relative to the represented family makes sense, and its component modules live on
the small étale sites of the representable algebraic spaces `yoneda.obj (T i)`.  This file carries
its pairwise isomorphisms to the underlying schemes:

`r_a^*(F_i|_{Zar}) ≅ r_b^*(F_j|_{Zar})`

for `a : Y ⟶ T i` and `b : Y ⟶ T j` agreeing over `U`, where `r_a`, `r_b` are the underlying
morphisms of schemes and `𝓕|_{Zar}` is
`AlgebraicGeometry.Space.representedZariskiModule`.  Together with the comparison
`AlgebraicGeometry.Space.representedZariskiModulePullbackIso` and its composition law this is the
data a quasi-coherent descent datum of Stacks 023B relative to the underlying family of schemes
is assembled from, which is where the effectivity of Stacks 023T can consume it.

Only the *pairwise* reading enters: a transition is read at an arbitrary test object of the big
fppf category over `S` along two morphisms to two members of the family, exactly as
`AlgebraicGeometry.Space.QuasiCoherentDescent.transitionOn` reads the transition of a descent
datum at an arbitrary test space.  **No associativity pentagon is used**, and the threefold
condition is the cocycle condition of the descent datum read at one representable test space.

## Main definitions

* `AlgebraicGeometry.Space.QuasiCoherentDescent.representedFamily` and `…representedFamilyMap`:
  the family of representable algebraic spaces of a family of the big fppf category over `S`.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.representedPairLift`: the morphism from a
  representable test space into a pairwise fibre product of that family induced by two morphisms
  agreeing over the target.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.zariskiTransitionOn`: **the pairwise isomorphism
  of a descent datum of a represented family, read on the underlying schemes.**

## Main results

* `AlgebraicGeometry.Space.QuasiCoherentDescent.representedPairLift_fst` and `…_snd`: its two
  projections are the two represented morphisms.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.zariskiTransitionOn_hom`: the comparison written
  out, so that a consumer rewrites rather than unfolds it.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.zariskiTransitionOn_self`: **read along one
  morphism twice it is the identity.**
* `AlgebraicGeometry.Space.QuasiCoherentDescent.zariskiTransitionOn_comp`: **the readings
  compose** — this is the cocycle condition of the descent datum at the representable test space.

## Implementation notes

The category of `𝒪`-modules of an algebraic space is
`AlgebraicGeometry.Space.Modules`, whose indexing ring sheaf is a projection of
`AlgebraicGeometry.Space.smallEtaleRingedSite`, while
`AlgebraicGeometry.Space.representedZariskiModule` is written in the spelling
`AlgebraicGeometry.Space.representedStructureRingSheaf` of that ring sheaf at a representable
algebraic space.  The two are the same, but not at the transparency at which a `rw` re-checks its
motive, so the coherence section makes that one definition locally `implicit_reducible`; nothing
else is relaxed, and every comparison is still handed over as an explicit term.

Under that relaxation the `rfl` proof of
`AlgebraicGeometry.Space.QuasiCoherentDescent.zariskiTransitionOn_hom` becomes unaffordable — it
is a delta-iota step underneath a `≫` of modules on a scheme — so the equation is proved by
rewriting the definition at the level of *isomorphisms*, where the step is cheap, and then
distributing `CategoryTheory.Iso.trans_hom` and `CategoryTheory.Functor.mapIso_hom`.

No `stacks` attribute is registered.  Stacks 04W3 is tagged where
`AlgebraicGeometry.Space.QuasiCoherentDescent.DescentDatum` is defined and Stacks 023B where the
quasi-coherent descent data of a family of schemes are; what is added here is the transport of the
first to the second, which is a step in the proof of Stacks 04W8.

## References

* [Stacks Project, Tag 04W3](https://stacks.math.columbia.edu/tag/04W3)
* [Stacks Project, Tag 023B](https://stacks.math.columbia.edu/tag/023B)
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
* [Stacks Project, Tag 04W8](https://stacks.math.columbia.edu/tag/04W8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AlgebraicGeometry.Space.QuasiCoherentDescent

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Represented

variable {I : Type v} {U : BigFppfOver B S hS} (T : I → BigFppfOver B S hS)
  (f : ∀ i, T i ⟶ U)

/-- The family of representable algebraic spaces over `S` of a family of the big fppf category
over `S`. -/
public abbrev representedFamily : I → AlgebraicSpaces B S hS :=
  fun i => representedAlgebraicSpace B S hS (T i)

/-- The structure morphisms of the family of representable algebraic spaces of a family of the
big fppf category over `S`. -/
public abbrev representedFamilyMap (i : I) :
    representedFamily B S hS T i ⟶ representedAlgebraicSpace B S hS U :=
  representedSpaceMap B S hS (f i)

section Lift

variable {Y : BigFppfOver B S hS} {q : Y ⟶ U} {i j : I} (a : Y ⟶ T i) (b : Y ⟶ T j)
  (ha : a ≫ f i = q) (hb : b ≫ f j = q)

include ha hb in
/-- Two morphisms of the big fppf category over `S` into two members of a family, agreeing over
the target, represent two morphisms of algebraic spaces agreeing over the target. -/
public theorem representedSpaceMap_comp_representedFamilyMap :
    representedSpaceMap B S hS a ≫ representedFamilyMap B S hS T f i =
      representedSpaceMap B S hS b ≫ representedFamilyMap B S hS T f j :=
  (representedSpaceMap_comp B S hS a (f i)).trans
    (((congrArg (fun z : Y ⟶ U => representedSpaceMap B S hS z) ha).trans
      (congrArg (fun z : Y ⟶ U => representedSpaceMap B S hS z) hb).symm).trans
      (representedSpaceMap_comp B S hS b (f j)).symm)

/-- **The morphism from a representable test space to the pairwise fibre product of the family of
representable algebraic spaces.**  For `a : Y ⟶ T i` and `b : Y ⟶ T j` of the big fppf category
over `S` agreeing over `U`, this is the morphism of algebraic spaces they induce into
`yoneda.obj (T i) ×_{yoneda.obj U} yoneda.obj (T j)`; it is what the pairwise isomorphism of a
descent datum is read along. -/
public noncomputable def representedPairLift :
    representedAlgebraicSpace B S hS Y ⟶
      pair B S hS (representedFamily B S hS T) (representedFamilyMap B S hS T f) i j :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS (representedFamilyMap B S hS T f i)
      (representedFamilyMap B S hS T f j)).lift (representedSpaceMap B S hS a)
    (representedSpaceMap B S hS b)
    (representedSpaceMap_comp_representedFamilyMap B S hS T f a b ha hb)

/-- The first projection of
`AlgebraicGeometry.Space.QuasiCoherentDescent.representedPairLift`. -/
public theorem representedPairLift_fst :
    representedPairLift B S hS T f a b ha hb ≫
        pairFst B S hS (representedFamily B S hS T) (representedFamilyMap B S hS T f) i j =
      representedSpaceMap B S hS a :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS (representedFamilyMap B S hS T f i)
    (representedFamilyMap B S hS T f j)).lift_fst _ _ _

/-- The second projection of
`AlgebraicGeometry.Space.QuasiCoherentDescent.representedPairLift`. -/
public theorem representedPairLift_snd :
    representedPairLift B S hS T f a b ha hb ≫
        pairSnd B S hS (representedFamily B S hS T) (representedFamilyMap B S hS T f) i j =
      representedSpaceMap B S hS b :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS (representedFamilyMap B S hS T f i)
    (representedFamilyMap B S hS T f j)).lift_snd _ _ _

end Lift

variable (D : DescentDatum B S hS (representedFamily B S hS T) (representedFamilyMap B S hS T f))

/-- **The pairwise isomorphism of a descent datum of a represented family, read on the underlying
schemes.**  For `a : Y ⟶ T i` and `b : Y ⟶ T j` of the big fppf category over `S` agreeing over
`U`, this compares the pullbacks along the underlying morphisms of schemes of the two modules on
the schemes underlying `T i` and `T j`.

It is `AlgebraicGeometry.Space.representedZariskiModulePullbackIso` below `a`, the restriction to
the small Zariski site of the pairwise isomorphism read along
`AlgebraicGeometry.Space.QuasiCoherentDescent.representedPairLift`, and the inverse of the
comparison below `b`. -/
public noncomputable def zariskiTransitionOn {Y : BigFppfOver B S hS} {q : Y ⟶ U} {i j : I}
    (a : Y ⟶ T i) (b : Y ⟶ T j) (ha : a ≫ f i = q) (hb : b ≫ f j = q) :
    (Scheme.Modules.pullback
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) a.left)).obj
        (representedZariskiModule B S hS (T i) (D.F i)) ≅
      (Scheme.Modules.pullback
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) b.left)).obj
        (representedZariskiModule B S hS (T j) (D.F j)) :=
  representedZariskiModulePullbackIso B S hS a (relativelyRepresentable_yoneda_map B S hS a)
      (D.F i) (D.quasicoherent i) ≪≫
    (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj Y) Y.left.property).mapIso
      ((representedSmallEtaleModuleEquivalence B S hS Y).inverse.mapIso
        (transitionOn B S hS (representedFamily B S hS T) (representedFamilyMap B S hS T f)
          D.F D.transition i j (representedPairLift B S hS T f a b ha hb)
          (representedSpaceMap B S hS a) (representedSpaceMap B S hS b)
          (representedPairLift_fst B S hS T f a b ha hb)
          (representedPairLift_snd B S hS T f a b ha hb))) ≪≫
    (representedZariskiModulePullbackIso B S hS b (relativelyRepresentable_yoneda_map B S hS b)
      (D.F j) (D.quasicoherent j)).symm

section Coherence

attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite

/-- `AlgebraicGeometry.Space.QuasiCoherentDescent.zariskiTransitionOn` as the composite of its
three pieces. -/
private theorem zariskiTransitionOn_eq_trans {Y : BigFppfOver B S hS} {q : Y ⟶ U} {i j : I}
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
          (relativelyRepresentable_yoneda_map B S hS b) (D.F j)
          (D.quasicoherent j)).symm := rfl

/-- `AlgebraicGeometry.Space.QuasiCoherentDescent.zariskiTransitionOn` written out, so that a
consumer rewrites with this equation instead of unfolding the definition underneath a `≫`. -/
public theorem zariskiTransitionOn_hom {Y : BigFppfOver B S hS} {q : Y ⟶ U} {i j : I}
    (a : Y ⟶ T i) (b : Y ⟶ T j) (ha : a ≫ f i = q) (hb : b ≫ f j = q) :
    (zariskiTransitionOn B S hS T f D a b ha hb).hom =
      (representedZariskiModulePullbackIso B S hS a
          (relativelyRepresentable_yoneda_map B S hS a) (D.F i)
          (D.quasicoherent i)).hom ≫
        (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj Y) Y.left.property).map
          (((representedSmallEtaleModuleEquivalence B S hS Y).inverse).map
            (transitionOn B S hS (representedFamily B S hS T)
                (representedFamilyMap B S hS T f) D.F D.transition i j
                (representedPairLift B S hS T f a b ha hb)
                (representedSpaceMap B S hS a) (representedSpaceMap B S hS b)
                (representedPairLift_fst B S hS T f a b ha hb)
                (representedPairLift_snd B S hS T f a b ha hb)).hom) ≫
        (representedZariskiModulePullbackIso B S hS b
            (relativelyRepresentable_yoneda_map B S hS b) (D.F j)
            (D.quasicoherent j)).inv := by
  rw [zariskiTransitionOn_eq_trans]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]

/-- **The transition of a descent datum of a represented family read along one morphism twice is
the identity.**  This is the cocycle condition at the triple `i, i, i`, through
`AlgebraicGeometry.Space.QuasiCoherentDescent.transitionOn_self`. -/
public theorem zariskiTransitionOn_self {Y : BigFppfOver B S hS} {q : Y ⟶ U} {i : I}
    (a : Y ⟶ T i) (ha : a ≫ f i = q) :
    zariskiTransitionOn B S hS T f D a a ha ha = Iso.refl _ := by
  rw [zariskiTransitionOn_eq_trans,
    transitionOn_self B S hS (representedFamily B S hS T) (representedFamilyMap B S hS T f) D i
      (representedPairLift B S hS T f a a ha ha) (representedSpaceMap B S hS a)
      (representedPairLift_fst B S hS T f a a ha ha)
      (representedPairLift_snd B S hS T f a a ha ha)]
  rw [Functor.mapIso_refl (representedSmallEtaleModuleEquivalence B S hS Y).inverse,
    Functor.mapIso_refl (_root_.AlgebraicGeometry.SmallEtale.restrictModule
      (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj Y) Y.left.property),
    Iso.refl_trans, Iso.self_symm_id]

/-- **The transitions of a descent datum of a represented family, read on the underlying schemes,
compose.**  For `a : Y ⟶ T i`, `b : Y ⟶ T j` and `c : Y ⟶ T k` of the big fppf category over `S`
all agreeing over `U`, the comparison from `a` to `b` followed by the one from `b` to `c` is the
one from `a` to `c`.

The comparison below `b` cancels against its inverse, and what is left is the cocycle condition of
the descent datum read at the representable test space `yoneda.obj Y` along the three morphisms
`AlgebraicGeometry.Space.QuasiCoherentDescent.representedPairLift` into the three pairwise fibre
products. -/
public theorem zariskiTransitionOn_comp {Y : BigFppfOver B S hS} {q : Y ⟶ U} {i j k : I}
    (a : Y ⟶ T i) (b : Y ⟶ T j) (c : Y ⟶ T k) (ha : a ≫ f i = q) (hb : b ≫ f j = q)
    (hc : c ≫ f k = q) :
    zariskiTransitionOn B S hS T f D a b ha hb ≪≫ zariskiTransitionOn B S hS T f D b c hb hc =
      zariskiTransitionOn B S hS T f D a c ha hc := by
  have hcoc : (transitionOn B S hS (representedFamily B S hS T)
          (representedFamilyMap B S hS T f) D.F D.transition i j
          (representedPairLift B S hS T f a b ha hb)
          (representedSpaceMap B S hS a) (representedSpaceMap B S hS b)
          (representedPairLift_fst B S hS T f a b ha hb)
          (representedPairLift_snd B S hS T f a b ha hb)).hom ≫
        (transitionOn B S hS (representedFamily B S hS T)
            (representedFamilyMap B S hS T f) D.F D.transition j k
            (representedPairLift B S hS T f b c hb hc)
            (representedSpaceMap B S hS b) (representedSpaceMap B S hS c)
            (representedPairLift_fst B S hS T f b c hb hc)
            (representedPairLift_snd B S hS T f b c hb hc)).hom =
      (transitionOn B S hS (representedFamily B S hS T)
          (representedFamilyMap B S hS T f) D.F D.transition i k
          (representedPairLift B S hS T f a c ha hc)
          (representedSpaceMap B S hS a) (representedSpaceMap B S hS c)
          (representedPairLift_fst B S hS T f a c ha hc)
          (representedPairLift_snd B S hS T f a c ha hc)).hom :=
    congrArg Iso.hom (D.cocycle i j k (representedAlgebraicSpace B S hS Y)
      (representedSpaceMap B S hS a) (representedSpaceMap B S hS b)
      (representedSpaceMap B S hS c) (representedPairLift B S hS T f a b ha hb)
      (representedPairLift B S hS T f b c hb hc) (representedPairLift B S hS T f a c ha hc)
      (representedPairLift_fst B S hS T f a b ha hb)
      (representedPairLift_snd B S hS T f a b ha hb)
      (representedPairLift_fst B S hS T f b c hb hc)
      (representedPairLift_snd B S hS T f b c hb hc)
      (representedPairLift_fst B S hS T f a c ha hc)
      (representedPairLift_snd B S hS T f a c ha hc))
  refine Iso.ext ?_
  rw [Iso.trans_hom, zariskiTransitionOn_hom, zariskiTransitionOn_hom,
    zariskiTransitionOn_hom, Category.assoc, Category.assoc, Iso.inv_hom_id_assoc,
    ← Functor.map_comp_assoc, ← Functor.map_comp, hcoc]

end Coherence

end Represented

end AlgebraicGeometry.Space.QuasiCoherentDescent

end
