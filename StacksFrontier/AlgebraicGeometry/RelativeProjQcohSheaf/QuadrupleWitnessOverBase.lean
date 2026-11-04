module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.AffineQuadrupleRoundTrip
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.QuadrupleWitness
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.UnionPullback

/-!
# Strict equivalence of quadruples over base morphisms that are equal rather than identical

Let `S` be a scheme, `𝒜` a graded `𝒪_S`-algebra (Situation 01NN) and `d` an integer. Strict
equivalence of quadruples (Section 01NS) is stated, and can only be stated, for two quadruples
over **literally the same** morphism `f : T ⟶ S`: the map `ψ` of a quadruple over `f` has source
`f^*𝒜^{(d)}`, so a comparison of two quadruples over two different morphisms is not even
type-correct.

A glueing argument meets a different situation. A family of charts `f i : Y i ⟶ S` with a
quadruple `P i` over each, compared over the overlap of two chart images, produces the two
chart pullbacks `(P i).pullback a_i` and `(P j).pullback a_j`, which lie over `a_i ≫ f i` and
`a_j ≫ f j`. Those two morphisms are **equal** — both are the inclusion of the overlap into `S` —
but they are not the same term, and `...RelativeProjQcohSheaf.Quadruple.StrictlyEquivalent` does
not apply to them.

`...RelativeProjQcohSheaf.Quadruple.congrBase` is the transport of a quadruple along an equality
of base morphisms, and it is all that is needed: this file reads strict equivalence through it
and carries the whole witness API of
`StacksFrontier/AlgebraicGeometry/RelativeProjQcohSheaf/QuadrupleWitness.lean` across. Nothing new
about the source is proved; the transport is pure bookkeeping, and every law below is the
corresponding law for a single base morphism after the equality has been substituted away.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple.StrictlyEquivalentOver`: **strict
  equivalence of two quadruples over base morphisms that are equal**, namely strict equivalence
  of the transport of the first along that equality with the second.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple.witnessOver`: **the canonical
  isomorphism `β : L ≅ L'` of the invertible modules of two such quadruples**, which is the
  comparison a glueing argument consumes.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple.witnessOver_trans`: **the canonical
  comparisons compose**, over three base morphisms that are only pairwise equal. This is the
  cocycle condition on a triple overlap, with no hypothesis beyond the pairwise equivalences, and
  it is the shape in which
  `Stacks.SheafOfModules.ModulesGlueData.exists_modulesGlueData_of_chartPullbackIso` asks for its
  comparisons.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple.witnessOver_refl` and
  `...Quadruple.witnessOver_symm`: the unit and inverse laws.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple.pullbackWitness`: **the comparison of
  the inverse images of the invertible modules of two quadruples pulled back to a common test
  scheme along morphisms whose composites with the two base morphisms agree.** This is
  `witnessOver` at the chart situation above, with the two base equalities read off the
  liftings.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple.StrictlyEquivalentOver.pullback` and
  `...Quadruple.witnessOver_pullback`: strict equivalence over equal base morphisms is preserved
  by pulling both quadruples back along a further morphism of test schemes, and **the comparison
  of the pullbacks is the inverse image of the comparison.**
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.laurentPullback_tensorPowerOneIso`: **the
  comparison of the integral tensor powers of Tag 01CU carries the identification `L^{⊗ 1} = L`
  in degree one**, which is the left-unit coherence of Tag 01CD; and
  `...RelativeProjQcohSheaf.laurentTransport_tensorPowerOneIso`, the same read on the transport
  of a degree-one comparison. These are what make `witness_pullback` true.

## What is not here

The cocycle **hypothesis** of
`Stacks.SheafOfModules.ModulesGlueData.exists_modulesGlueData_of_chartPullbackIso` is not yet
discharged from `witnessOver_trans` and `witnessOver_pullback`. That hypothesis compares the
comparisons restricted to a triple overlap through
`Stacks.SheafOfModules.chartPullbackRestrict`, which is
`Stacks.AlgebraicGeometry.ModuleHomGlue.pullbackChartRestrict` — assembled from
`AlgebraicGeometry.Scheme.Modules.pullbackComp` and `...pullbackCongr` — and not the inverse
image along a single morphism that `witnessOver_pullback` produces. Identifying the two is the
step still owed; the quadruple side of it is complete.

## No tag is claimed

Section 01NS states strict equivalence for quadruples over one morphism; reading it through a
transport adds nothing to the source.

## References

* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01NV](https://stacks.math.columbia.edu/tag/01NV)
-/

@[expose] public noncomputable section

open CategoryTheory

open AlgebraicGeometry Stacks.RingedSpace

open Stacks.SheafOfModules.TensorPower

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

variable {T'' T' T S : Scheme.{u}}

/-! ### The comparison of the integral tensor powers in degree one -/

/-- **A conjugation cancelled, with every object and morphism free.** A composite built from two
isomorphisms `o`, `o'` and a morphism `b` between their targets, pushed through a functor and
conjugated by two isomorphisms `l`, `l'` that the functor's images of `o` and `o'` factor
through, is the image of `b` conjugated by the remaining two isomorphisms.

Stated abstractly because the concrete instance mixes the two spellings
`Stacks.SheafOfModules.TensorSheafification.structureSheaf` and
`Stacks.RingedSpace.structureRingSheaf` of the structure sheaf: a goal containing both is not
type-correct at `implicit` transparency, so every rewriting tactic refuses it. Applying a helper
with free arrows by `exact` crosses the definitional equality once. -/
private theorem map_conj_cancel {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B A' B' : C} {A₁ A₁' : D} (o : A ≅ B) (o' : A' ≅ B') (b : B ⟶ B')
    (l : F.obj A ≅ A₁) (l' : F.obj A' ≅ A₁') (o₁ : A₁ ≅ F.obj B) (o₁' : A₁' ≅ F.obj B')
    (h : F.map o.hom = l.hom ≫ o₁.hom) (h' : F.map o'.hom = l'.hom ≫ o₁'.hom) :
    l.inv ≫ F.map (o.hom ≫ b ≫ o'.inv) ≫ l'.hom = o₁.hom ≫ F.map b ≫ o₁'.inv := by
  have hinv : F.map o'.inv ≫ l'.hom = o₁'.inv := by
    rw [show F.map o'.inv = (F.mapIso o').inv from rfl,
      show F.mapIso o' = l' ≪≫ o₁' from Iso.ext h']
    simp
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, h]
  simp only [Category.assoc]
  rw [hinv, Iso.inv_hom_id_assoc]

/-- **The comparison `g^*(L^{⊗ n}) ≅ (g^*L)^{⊗ n}` of the integral tensor powers of Tag 01CU
carries the identification `L^{⊗ 1} = L` in degree one.** That identification is the left unit
constraint of Tag 01CA, so this is the compatibility of the comparison of Tag 01CD with the left
unit constraints, which is
`Stacks.TensorPowerPullback.isLeftUnital_pullback`; the passage from that compatibility to this
statement is
`Stacks.SheafOfModules.TensorPower.map_tensorPowerOneIso_tensorPowerComparison`, and the
comparison of tensor powers determined by the tensorator of Tag 01CD is `laurentPullback` by
`rfl` (`Stacks.TensorPowerPullback.tensorPowerComparison_eq_pullbackIntPowIso`). -/
theorem laurentPullback_tensorPowerOneIso (g : T' ⟶ T)
    (L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))
    [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L] :
    (pullbackFunctor (ringedSpaceHom g)).map
        (tensorPowerOneIso T.toRingedSpace.presheaf (isSheafStruct T) L).hom =
      laurentPullback g L 1 ≫
        (tensorPowerOneIso T'.toRingedSpace.presheaf (isSheafStruct T')
          ((pullbackFunctor (ringedSpaceHom g)).obj L)).hom :=
  map_tensorPowerOneIso_tensorPowerComparison T.toRingedSpace.presheaf (isSheafStruct T)
    T'.toRingedSpace.presheaf (isSheafStruct T') (pullbackFunctor (ringedSpaceHom g)) L
    (Stacks.TensorPowerPullback.pullbackTensorator (ringedSpaceHom g))
    (Stacks.TensorPowerPullback.pullbackUnitSheafIso (ringedSpaceHom g))
    (Stacks.TensorPowerPullback.isLeftUnital_pullback (ringedSpaceHom g))

/-- **The transport of a degree-one comparison along a morphism of test schemes is the inverse
image of the morphism of invertible modules it comes from.** A morphism `L^{⊗ 1} ⟶ (L')^{⊗ 1}`
read through the identifications `L^{⊗ 1} = L` and `(L')^{⊗ 1} = L'` of Tag 01CU is transported
to the inverse image of `b` read through the same identifications for `g^*L` and `g^*L'`: the
two comparisons of the integral tensor powers that `laurentTransport` cancels are exactly the
ones `laurentPullback_tensorPowerOneIso` produces.

The `IsIso` instance of the comparison is handed to `CategoryTheory.asIso` explicitly:
instance search does not reach `...RelativeProjQcohSheaf.isIso_laurentPullback` from the goal
`IsIso (laurentPullback g L 1)`, while the explicit application elaborates. -/
theorem laurentTransport_tensorPowerOneIso (g : T' ⟶ T)
    (L L' : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))
    [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]
    [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L']
    (b : L ⟶ L') :
    laurentTransport g L L' 1 1
        ((tensorPowerOneIso T.toRingedSpace.presheaf (isSheafStruct T) L).hom ≫ b ≫
          (tensorPowerOneIso T.toRingedSpace.presheaf (isSheafStruct T) L').inv) =
      (tensorPowerOneIso T'.toRingedSpace.presheaf (isSheafStruct T')
            ((pullbackFunctor (ringedSpaceHom g)).obj L)).hom ≫
        (pullbackFunctor (ringedSpaceHom g)).map b ≫
          (tensorPowerOneIso T'.toRingedSpace.presheaf (isSheafStruct T')
            ((pullbackFunctor (ringedSpaceHom g)).obj L')).inv :=
  map_conj_cancel (pullbackFunctor (ringedSpaceHom g))
    (tensorPowerOneIso T.toRingedSpace.presheaf (isSheafStruct T) L)
    (tensorPowerOneIso T.toRingedSpace.presheaf (isSheafStruct T) L') b
    (@asIso _ _ _ _ (laurentPullback g L 1) (isIso_laurentPullback g L 1))
    (@asIso _ _ _ _ (laurentPullback g L' 1) (isIso_laurentPullback g L' 1))
    (tensorPowerOneIso T'.toRingedSpace.presheaf (isSheafStruct T')
      ((pullbackFunctor (ringedSpaceHom g)).obj L))
    (tensorPowerOneIso T'.toRingedSpace.presheaf (isSheafStruct T')
      ((pullbackFunctor (ringedSpaceHom g)).obj L'))
    (laurentPullback_tensorPowerOneIso g L) (laurentPullback_tensorPowerOneIso g L')

namespace Quadruple

variable {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)} {d : ℤ}

/-! ### The canonical comparison and a further pullback -/

/-- **The canonical comparison of two strictly equivalent quadruples is compatible with pulling
both of them back along a morphism of test schemes**: the comparison of the pullbacks is the
inverse image of the comparison.

By `...RelativeProjQcohSheaf.Quadruple.witness_eq` it is enough to exhibit *some* witness of the
strict equivalence of the pullbacks whose degree-one component is the inverse image of
`witness h`, and `...RelativeProjQcohSheaf.laurentPullbackIso` applied to
`...RelativeProjQcohSheaf.Quadruple.laurentWitness` is one: the compatibility with `ψ` is
`...RelativeProjQcohSheaf.Twisting.pullbackApp_comp_laurentTransport_of_app` and the degree-one
clause is `...RelativeProjQcohSheaf.laurentTransport_tensorPowerOneIso`. -/
theorem witness_pullback {f : T ⟶ S}
    {P Q : Quadruple f A d} (h : StrictlyEquivalent P Q) (g : T' ⟶ T)
    (h' : StrictlyEquivalent (P.pullback g) (Q.pullback g)) :
    witness h' = (pullbackFunctor (ringedSpaceHom g)).mapIso (witness h) :=
  witness_eq h' (γ := laurentPullbackIso g (laurentWitness h))
    (by
      show laurentTransport g P.L Q.L 1 1 ((laurentWitness h).hom.app 1) = _
      rw [laurentWitness_app_one h]
      exact laurentTransport_tensorPowerOneIso g P.L Q.L (witness h).hom)
    fun n => Twisting.pullbackApp_comp_laurentTransport_of_app P.twisting Q.twisting g n
      ((laurentWitness h).hom.app n) (twisting_app_comp_laurentWitness h n)

/-! ### The transport along an equality of base morphisms, on the data of a quadruple -/

/-- Transporting a quadruple along the reflexivity of its own base morphism changes nothing. -/
@[simp] theorem congrBase_rfl {g : T ⟶ S} (P : Quadruple g A d) :
    congrBase (rfl : g = g) P = P :=
  congrBase_eq rfl P P rfl HEq.rfl

/-- **Transport along an equality of base morphisms does not change the invertible module.** The
field `L` of a quadruple does not mention the base morphism; only `twisting` does. -/
theorem congrBase_L {g g' : T ⟶ S} (h : g = g') (P : Quadruple g A d) :
    (congrBase h P).L = P.L := by
  subst h
  rfl

/-- The identification of the invertible module of a transported quadruple with the invertible
module of the quadruple it was transported from. -/
def congrBaseLIso {g g' : T ⟶ S} (h : g = g') (P : Quadruple g A d) :
    (congrBase h P).L ≅ P.L :=
  eqToIso (congrBase_L h P)

/-- Along the reflexivity of the base morphism, the identification `congrBaseLIso` is the
identity of the invertible module. -/
@[simp] theorem congrBaseLIso_rfl {g : T ⟶ S} (P : Quadruple g A d) :
    congrBaseLIso (rfl : g = g) P = Iso.refl P.L :=
  eqToIso_refl (congrBase_L (rfl : g = g) P)

/-! ### Strict equivalence over equal base morphisms -/

/-- **Strict equivalence of two quadruples over base morphisms that are equal rather than
identical**: strict equivalence of the transport of the first along the equality with the second.

This is the relation a glueing argument has over the overlap of two charts, where the two
quadruples are chart pullbacks lying over `a_i ≫ f i` and `a_j ≫ f j`. -/
def StrictlyEquivalentOver {g g' : T ⟶ S} (h : g = g') (P : Quadruple g A d)
    (Q : Quadruple g' A d) : Prop :=
  StrictlyEquivalent (congrBase h P) Q

/-- Over one base morphism, strict equivalence over equal base morphisms is strict
equivalence. -/
theorem strictlyEquivalentOver_rfl_iff {g : T ⟶ S} (P Q : Quadruple g A d) :
    StrictlyEquivalentOver (rfl : g = g) P Q ↔ StrictlyEquivalent P Q := by
  rw [StrictlyEquivalentOver, congrBase_rfl]

/-- **Every quadruple is strictly equivalent to itself over the reflexivity of its base
morphism.** -/
theorem strictlyEquivalentOver_refl {g : T ⟶ S} (P : Quadruple g A d) :
    StrictlyEquivalentOver (rfl : g = g) P P :=
  (strictlyEquivalentOver_rfl_iff P P).mpr (strictlyEquivalent_equivalence.refl P)

/-- **Strict equivalence over equal base morphisms is symmetric**, along the symmetric
equality. -/
theorem StrictlyEquivalentOver.symm {g g' : T ⟶ S} {h : g = g'} {P : Quadruple g A d}
    {Q : Quadruple g' A d} (e : StrictlyEquivalentOver h P Q) :
    StrictlyEquivalentOver h.symm Q P := by
  subst h
  exact strictlyEquivalent_equivalence.symm e

/-- **Strict equivalence over equal base morphisms is transitive**, along the composite
equality. -/
theorem StrictlyEquivalentOver.trans {g g' g'' : T ⟶ S} {h : g = g'} {h' : g' = g''}
    {P : Quadruple g A d} {Q : Quadruple g' A d} {R : Quadruple g'' A d}
    (e : StrictlyEquivalentOver h P Q) (e' : StrictlyEquivalentOver h' Q R) :
    StrictlyEquivalentOver (h.trans h') P R := by
  subst h'
  subst h
  exact strictlyEquivalent_equivalence.trans e e'

/-! ### The canonical comparison and its three laws -/

/-- **The canonical isomorphism `β : L ≅ L'` of the invertible modules of two quadruples
strictly equivalent over equal base morphisms.** It is
`...RelativeProjQcohSheaf.Quadruple.witness` of the transported pair, read through the
identification `congrBaseLIso` of the invertible module of the transport with the original one.

This is the comparison a glueing argument consumes: over the overlap of two charts it is an
isomorphism of the inverse images of the two chart modules. -/
def witnessOver {g g' : T ⟶ S} {h : g = g'} {P : Quadruple g A d} {Q : Quadruple g' A d}
    (e : StrictlyEquivalentOver h P Q) : P.L ≅ Q.L :=
  (congrBaseLIso h P).symm ≪≫ witness e

/-- Over one base morphism the canonical comparison over equal base morphisms is the canonical
comparison. -/
theorem witnessOver_rfl {g : T ⟶ S} {P Q : Quadruple g A d}
    (e : StrictlyEquivalentOver (rfl : g = g) P Q) :
    witnessOver e = witness ((strictlyEquivalentOver_rfl_iff P Q).mp e) := by
  rw [witnessOver, congrBaseLIso_rfl]
  exact Iso.ext (Category.id_comp _)

/-- **The canonical comparison of a quadruple with itself is the identity.** -/
@[simp] theorem witnessOver_refl {g : T ⟶ S} {P : Quadruple g A d}
    (e : StrictlyEquivalentOver (rfl : g = g) P P) : witnessOver e = Iso.refl P.L :=
  (witnessOver_rfl e).trans (witness_refl _)

/-- **The canonical comparisons compose, over three base morphisms that are only pairwise
equal.** For a family of quadruples on the members of an open covering of a test scheme, pairwise
strictly equivalent on the overlaps, this is the cocycle condition on the triple overlaps, and it
holds with no hypothesis beyond the pairwise equivalences: the comparisons are not chosen but
determined.

As in `...RelativeProjQcohSheaf.Quadruple.witness_trans`, the three proofs of strict equivalence
are unrelated arguments rather than the third being derived from the first two; strict
equivalence is a `Prop`, so this makes the statement no weaker. -/
theorem witnessOver_trans {g g' g'' : T ⟶ S} {h : g = g'} {h' : g' = g''}
    {P : Quadruple g A d} {Q : Quadruple g' A d} {R : Quadruple g'' A d}
    (e : StrictlyEquivalentOver h P Q) (e' : StrictlyEquivalentOver h' Q R)
    (e'' : StrictlyEquivalentOver (h.trans h') P R) :
    witnessOver e ≪≫ witnessOver e' = witnessOver e'' := by
  subst h'
  subst h
  rw [witnessOver_rfl, witnessOver_rfl, witnessOver_rfl]
  exact witness_trans _ _ _

/-- **The canonical comparison in the opposite direction is the inverse.** -/
theorem witnessOver_symm {g g' : T ⟶ S} {h : g = g'} {h' : g' = g}
    {P : Quadruple g A d} {Q : Quadruple g' A d} (e : StrictlyEquivalentOver h P Q)
    (e' : StrictlyEquivalentOver h' Q P) : witnessOver e' = (witnessOver e).symm := by
  subst h
  rw [witnessOver_rfl, witnessOver_rfl]
  exact witness_symm _ _

/-! ### The chart situation: two quadruples pulled back to a common test scheme -/

/-- **Strict equivalence over equal base morphisms is preserved by pulling both quadruples back
along a further morphism of test schemes.** The two base morphisms become `c ≫ g` and `c ≫ g'`,
still equal; this is `...RelativeProjQcohSheaf.Quadruple.StrictlyEquivalent.pullback` after the
equality has been substituted away. -/
theorem StrictlyEquivalentOver.pullback {g g' : T ⟶ S} {h : g = g'} {P : Quadruple g A d}
    {Q : Quadruple g' A d} (e : StrictlyEquivalentOver h P Q) (c : T' ⟶ T) :
    StrictlyEquivalentOver (congrArg (fun z => c ≫ z) h) (P.pullback c) (Q.pullback c) := by
  subst h
  exact StrictlyEquivalent.pullback e c

/-- **The canonical comparison over equal base morphisms is compatible with a further
pullback.** This is `...RelativeProjQcohSheaf.Quadruple.witness_pullback` after the equality of
base morphisms has been substituted away, and it is what a cocycle condition stated on a smaller
open of the base needs: the comparison of the restricted quadruples is the inverse image of the
comparison. -/
theorem witnessOver_pullback {g g' : T ⟶ S} {h : g = g'} {P : Quadruple g A d}
    {Q : Quadruple g' A d} (e : StrictlyEquivalentOver h P Q) {c : T' ⟶ T}
    {h' : c ≫ g = c ≫ g'}
    (e' : StrictlyEquivalentOver h' (P.pullback c) (Q.pullback c)) :
    witnessOver e' = (pullbackFunctor (ringedSpaceHom c)).mapIso (witnessOver e) := by
  subst h
  refine (witnessOver_rfl e').trans ?_
  refine (witness_pullback ((strictlyEquivalentOver_rfl_iff P Q).mp e) c _).trans ?_
  exact congrArg (pullbackFunctor (ringedSpaceHom c)).mapIso (witnessOver_rfl e).symm

/-- **The comparison of the inverse images of the invertible modules of two quadruples pulled
back to a common test scheme.** Let `P` be a quadruple over `f : T ⟶ S` and `P'` one over
`f' : T' ⟶ S`, and let `a : W ⟶ T` and `b : W ⟶ T'` satisfy `a ≫ f = b ≫ f'`. The two pullbacks
`P.pullback a` and `P'.pullback b` are quadruples over those two equal morphisms `W ⟶ S`, and a
strict equivalence of them over that equality is an isomorphism `a^*L ≅ b^*L'`.

This is the shape in which the comparison of two chart quadruples over the overlap of the chart
images arrives, and it is what
`Stacks.SheafOfModules.ModulesGlueData.exists_modulesGlueData_of_chartPullbackIso` consumes: the
two liftings `a` and `b` of an open of `S` inside both chart images satisfy exactly that equation
with the two chart morphisms. -/
def pullbackWitness {f : T ⟶ S} {f' : T' ⟶ S} {a : T'' ⟶ T} {b : T'' ⟶ T'}
    {h : a ≫ f = b ≫ f'} {P : Quadruple f A d} {P' : Quadruple f' A d}
    (e : StrictlyEquivalentOver h (P.pullback a) (P'.pullback b)) :
    (pullbackFunctor (ringedSpaceHom a)).obj P.L ≅
      (pullbackFunctor (ringedSpaceHom b)).obj P'.L :=
  witnessOver e

/-- **The comparisons of three quadruples pulled back to a common test scheme compose.** This is
`witnessOver_trans` at the chart situation of `pullbackWitness`: on an open of `S` contained in
three chart images, the comparison of the first chart with the second followed by the comparison
of the second with the third is the comparison of the first with the third. -/
theorem pullbackWitness_trans {T₃ : Scheme.{u}} {f : T ⟶ S} {f' : T' ⟶ S} {f'' : T₃ ⟶ S}
    {a : T'' ⟶ T} {b : T'' ⟶ T'} {c : T'' ⟶ T₃}
    {h : a ≫ f = b ≫ f'} {h' : b ≫ f' = c ≫ f''}
    {P : Quadruple f A d} {P' : Quadruple f' A d} {P'' : Quadruple f'' A d}
    (e : StrictlyEquivalentOver h (P.pullback a) (P'.pullback b))
    (e' : StrictlyEquivalentOver h' (P'.pullback b) (P''.pullback c))
    (e'' : StrictlyEquivalentOver (h.trans h') (P.pullback a) (P''.pullback c)) :
    pullbackWitness e ≪≫ pullbackWitness e' = pullbackWitness e'' :=
  witnessOver_trans e e' e''

end Quadruple

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
