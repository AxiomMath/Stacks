module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.FamilyPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.FpqcChartLocalization
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.MemberSiteDatumSheaf

/-!
# The canonical descent datum of a refinement

Let `X` be an algebraic space over a scheme `S` of a big fppf site, let `𝒱 = {V j ⟶ X}` be a
family of algebraic spaces over `X` and let `𝒰 = {U i ⟶ X}` be a refinement of it in the sense of
Stacks 00VT (2), that is a morphism of families over the identity of `X`.  For a quasi-coherent
`𝒪_X`-module `M` the canonical descent datum of Stacks 04W5 of `M` relative to `𝒰` and the
pullback along the refinement of its canonical descent datum relative to `𝒱` have component
modules `(U i ⟶ X)^*M` and `(U i ⟶ V (s₀ i))^*(V (s₀ i) ⟶ X)^*M`, which are canonically
isomorphic.  This file proves that those isomorphisms commute with the pairwise isomorphisms of
the two data, so that the two descent data agree.

This is steps (1) and (3) of the proof of Stacks 04W8: step (1) is the canonical descent functor
of a family, which is
`AlgebraicGeometry.Space.QuasiCoherentDescent.canonicalDescentFunctor'`, and step (3) is the
passage to a refinement, for which the source cites Stacks 04W4 —
`AlgebraicGeometry.Space.QuasiCoherentDescent.pullbackDatum` and `…pullbackFunctor` of
`StacksFrontier/AlgebraicGeometry/Spaces/Descent/QuasiCoherent/FamilyPullback.lean`, which carry no
hypothesis — and Stacks 0419, `AlgebraicGeometry.Space.exists_fpqc_scheme_refinement`, which
refines an fpqc covering of algebraic spaces by one whose members are schemes.

For a morphism of families over an arbitrary morphism `g : X ⟶ Y` of their two targets the same
comparison exists, between the pullback along it of the canonical descent datum of an
`𝒪_Y`-module `M` and the canonical descent datum of `g^*M`; that is the form in which
Stacks 04W4 and Stacks 04W5 are compared, and the refinement is its case `g = 𝟙 X` only after
`M` is identified with `(𝟙 X)^*M`.  Both are proved here.

## Main definitions

* `AlgebraicGeometry.Space.QuasiCoherentDescent.DescentDatum.isoMkOfTransitionEq` builds an
  isomorphism of descent data from a compatibility stated at *named* pairwise isomorphisms and on
  isomorphisms rather than on their underlying morphisms.  The family of isomorphisms of the
  component modules is assembled by
  `AlgebraicGeometry.Space.QuasiCoherentDescent.DescentDatum.isoMk`, which this file does not
  restate.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.refinementComparison` is the canonical
  isomorphism of the two component modules, and
  `…canonicalDescentDatumRefinementIso` is the isomorphism of descent data it assembles into.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.canonicalDescentDatumPullbackIso` is the
  isomorphism of descent data for a morphism of families over an arbitrary morphism of their
  targets, whose comparison of the component modules is a canonical comparison of two inverse
  images and needs no name of its own.

## Main results

* `CategoryTheory.Iso.inv_comp_eq_comp_inv_of_comp_eq`: a commuting square of isomorphisms,
  solved for the two inverse arrows.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.canonicalComparison_factorLeft` and
  `…canonicalComparison_factorRight`: **the canonical comparison of two inverse images of
  Stacks 04W5 against a factorization of either of its two legs.**  These are the associativity
  coherence of the comparison of inverse images of Stacks 03LU, in the form the refinement
  needs, and they carry no hypothesis: that coherence is
  `AlgebraicGeometry.Space.modulePullbackCompIsoAssoc`
  (`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePushforwardCompIsoAssoc.lean:339`).
  Nothing in this file takes it as an argument.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.pullbackTransition_canonicalDescentDatum'`: the
  pulled-back pairwise isomorphism of a canonical descent datum is again a canonical comparison,
  for the two legs composed with the `h₀` of the morphism of families.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.canonicalComparison_pullbackTransition`: **the
  canonical comparison of the component modules commutes with the pairwise isomorphisms**, for a
  morphism of families over an arbitrary morphism of their targets.  This is what
  `…canonicalDescentDatumPullbackIso` assembles.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.refinementComparison_transition`,
  `…refinementComparison_naturality` and `…refinementComparison_inv_naturality`: **the
  comparison of the canonical descent datum of a refining family with the pullback along the
  refinement of the canonical descent datum of the refined family commutes with the pairwise
  isomorphisms of Stacks 04W3**, as an equality of isomorphisms and in the two readings on
  morphisms.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.canonicalDescentDatumRefinementIso`: **the
  canonical descent datum of a refining family *is* the pullback along the refinement of the
  canonical descent datum of the refined family**, as an isomorphism in the category of descent
  data of Stacks 04W3.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.isEffective_pullbackDatum`,
  `…isEffective_of_isEffective_pullbackDatum`, `…isEffective_pullbackDatum_iff` and
  `…isEffective_of_forall_isEffective`: **the refinement transport of effectivity.**  The easy
  half carries nothing; the hard half takes full faithfulness of pullback along the refinement,
  which is where descent of morphisms enters, and nothing else.  This is the space-level
  counterpart of
  `…isEffective_of_isEffective_pullFunctor_obj_of_bijective` in the namespace
  `AlgebraicGeometry.QuasicoherentDescentData`
  (`StacksFrontier/AlgebraicGeometry/Descent/QuasiCoherent/RefinementTransport.lean`).

## Implementation notes

Every statement about the comparisons is an equality of *isomorphisms* and is instantiated at
variable isomorphisms wherever a cancellation is performed; that is the discipline of
`StacksFrontier/AlgebraicGeometry/Spaces/Descent/QuasiCoherent/Canonical.lean`, and
`CategoryTheory.Iso.inv_comp_eq_comp_inv_of_comp_eq` is here for exactly that reason.

The three compatibility statements are written out at
`AlgebraicGeometry.Space.QuasiCoherentDescent.pullbackTransition` and
`…canonicalComparison` rather than at the `transition` projections of the two descent data, so
they are not in the shape the compatibility field of
`AlgebraicGeometry.Space.QuasiCoherentDescent.DescentDatum.Hom` asks for.  **The reconciliation
has to happen on isomorphisms, and that is what
`AlgebraicGeometry.Space.QuasiCoherentDescent.DescentDatum.isoMkOfTransitionEq` is for.**  The two
shapes differ by one delta-iota step in each object argument, and underneath `≫` that step is not
affordable: it is a kernel deterministic timeout, both when the two spellings are
reconciled by `rw` at the two `transition` simp lemmas and when they are reconciled by a bare
`exact` in a declaration carrying nothing else.  This is the obstruction that the implementation
notes of
`StacksFrontier/AlgebraicGeometry/Spaces/Descent/QuasiCoherent/FamilyPullback.lean` record for
`AlgebraicGeometry.Space.QuasiCoherentDescent.pullbackCompare`: composition in the category of
modules is a projection of the `SheafOfModules` instance and is projection-reduced before
congruence is attempted, so an identification underneath a `≫` at these types is not affordable.

`CategoryTheory.Iso.trans` and `CategoryTheory.Functor.mapIso` are ordinary definitions and not
projections, so congruence on their arguments is attempted first and the same step is free there.
`isoMkOfTransitionEq` therefore takes the compatibility as an equality of *isomorphisms* at named
pairwise isomorphisms, identifies those with the `transition` fields by two hypotheses which the
consumer discharges with the `rfl` simp lemmas `…canonicalDescentDatum'_transition` and
`…pullbackDatum_transition`, and extracts the underlying morphisms afterwards by
`CategoryTheory.Iso.trans_hom` and `CategoryTheory.Functor.mapIso_hom` — whose instances carry the
object arguments of the projected shape, so nothing is left to convert.  It is stated at variable
descent data and variable pairwise isomorphisms, so the kernel is asked for no reduction in it at
all, and `AlgebraicGeometry.Space.QuasiCoherentDescent.canonicalDescentDatumRefinementIso`
instantiates it with `…refinementComparison_transition` unchanged.

The module universe is the universe of the structure rings, because
`AlgebraicGeometry.Space.modulePullback` exists only there.

## References

* [Stacks Project, Tag 04W8](https://stacks.math.columbia.edu/tag/04W8)
* [Stacks Project, Tag 04W5](https://stacks.math.columbia.edu/tag/04W5)
* [Stacks Project, Tag 04W4](https://stacks.math.columbia.edu/tag/04W4)
* [Stacks Project, Tag 04W3](https://stacks.math.columbia.edu/tag/04W3)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 0419](https://stacks.math.columbia.edu/tag/0419)
* [Stacks Project, Tag 00VT](https://stacks.math.columbia.edu/tag/00VT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Iso

universe v₁ u₁

variable {C : Type u₁} [Category.{v₁} C]

/-- A commuting square of isomorphisms, solved for the two inverse arrows: from
`A ≫ E = D ≫ G` with all four invertible, `A⁻¹ ≫ D = E ≫ G⁻¹`.

This is Mathlib's `CategoryTheory.CommSq.horiz_inv` and is proved by it, not re-proved: the
content is entirely Mathlib's.  What this adds is the interface, and only that.  The four
isomorphisms are named arguments at a variable category, so a consumer whose four isomorphisms
are comparisons of inverse images of modules instantiates it with no reduction; asking such a
consumer to build the `CommSq` itself asks the elaborator to normalize a composite at those
types, which is the reduction the paragraph below records as not finishing.

`AlgebraicGeometry.Space.QuasiCoherentDescent.inv_naturality` is the same cancellation with the
two middle arrows carried as plain morphisms and all four arguments explicit, and it is not what
the one consumer here can use: instantiated at these comparisons, its argument order assigns the
two `CategoryTheory.Functor.mapIso` before the two named comparisons, and the identification of
`(F.mapIso e).inv` with `F.map e.inv` underneath `≫` that this forces is a kernel
deterministic timeout.  With the order below the same proof checks at once. -/
theorem inv_comp_eq_comp_inv_of_comp_eq {W X Y Z : C} {A : W ≅ X} {E : X ≅ Z} {D : W ≅ Y}
    {G : Y ≅ Z} (h : A.hom ≫ E.hom = D.hom ≫ G.hom) : A.inv ≫ D.hom = E.hom ≫ G.inv :=
  (CategoryTheory.CommSq.horiz_inv (f := A) (i := G) (CategoryTheory.CommSq.mk h)).w

end CategoryTheory.Iso

universe u v v'

namespace AlgebraicGeometry.Space.QuasiCoherentDescent

/-- The first-argument companion of
`AlgebraicGeometry.Space.QuasiCoherentDescent.modulePullbackCompIso_eqToIso`: transporting
along an equality of the *inner* morphism commutes with the comparison of iterated inverse
images, which turns the transport of the iterated inverse image into the transport of the
inverse image along the composite.

It is stated as the commutation rather than as a composite of three equal to one transport,
because that is the shape in which it occurs inside a longer composite of isomorphisms, where
`CategoryTheory.Iso.subst_trans₂` consumes it. -/
theorem modulePullbackCompIso_eqToIso_left {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} {A P T : AlgebraicSpaces B S hS} {g g' : T ⟶ P}
    (h : g = g') (p : P ⟶ A) (M : Modules.{u, u} B S hS A.1 A.2) :
    ((modulePullbackCompIso B S hS g p).app M).symm ≪≫
        eqToIso (congrArg (fun r : T ⟶ P => (modulePullback B S hS r).obj
          ((modulePullback B S hS p).obj M)) h) =
      eqToIso (congrArg (fun r : T ⟶ P => (modulePullback B S hS (r ≫ p)).obj M) h) ≪≫
        ((modulePullbackCompIso B S hS g' p).app M).symm := by
  cases h
  apply Iso.ext
  simp

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

namespace DescentDatum

variable {I : Type v} {X : AlgebraicSpaces B S hS} {Y : I → AlgebraicSpaces B S hS}
  {f : ∀ i, Y i ⟶ X}

/-- **An isomorphism of descent data whose compatibility is supplied at named pairwise
isomorphisms**, together with the identification of those with the `transition` fields of the two
data, and as an equality of *isomorphisms* rather than of their underlying morphisms.

This is the form in which a compatibility proved about written-out pairwise isomorphisms — such
as `AlgebraicGeometry.Space.QuasiCoherentDescent.refinementComparison_transition` — is assembled
into an isomorphism of descent data.  The written-out shape and the shape the compatibility field
of `AlgebraicGeometry.Space.QuasiCoherentDescent.DescentDatum.Hom` asks for differ by one
delta-iota step in each object argument, and underneath `≫` that step is not affordable:
`CategoryTheory.CategoryStruct.comp` is a projection of the category instance of the modules on
the small étale site of an algebraic space, so the kernel projection-reduces it before attempting
congruence on the arguments, and does not come back.  `CategoryTheory.Iso.trans` and
`CategoryTheory.Functor.mapIso` are ordinary definitions, congruence on their arguments is
attempted first, and the same step is free there — which is why `h` is stated on isomorphisms.

Everything here is at variable descent data and variable pairwise isomorphisms, so the kernel is
asked for no reduction in this declaration at all; a consumer instantiating it pays only for
matching the isomorphisms. -/
def isoMkOfTransitionEq {D E : DescentDatum B S hS Y f} (e : ∀ i, D.F i ≅ E.F i)
    (TD : ∀ i j, (modulePullback B S hS (pairFst B S hS Y f i j)).obj (D.F i) ≅
      (modulePullback B S hS (pairSnd B S hS Y f i j)).obj (D.F j))
    (TE : ∀ i j, (modulePullback B S hS (pairFst B S hS Y f i j)).obj (E.F i) ≅
      (modulePullback B S hS (pairSnd B S hS Y f i j)).obj (E.F j))
    (hD : ∀ i j, D.transition i j = TD i j) (hE : ∀ i j, E.transition i j = TE i j)
    (h : ∀ i j, (modulePullback B S hS (pairFst B S hS Y f i j)).mapIso (e i) ≪≫ TE i j =
      TD i j ≪≫ (modulePullback B S hS (pairSnd B S hS Y f i j)).mapIso (e j)) :
    D ≅ E :=
  isoMk B S hS Y f e fun i j => by
    rw [hD i j, hE i j]
    simpa only [Iso.trans_hom, Functor.mapIso_hom] using congrArg Iso.hom (h i j)

end DescentDatum

/-- Factoring the first leg of a canonical comparison. -/
theorem canonicalComparison_factorLeft
    {A P Q Q' R : AlgebraicSpaces B S hS} (p : P ⟶ Q) (u : Q ⟶ Q') (fi : Q' ⟶ A)
    (gi : Q ⟶ A) (hgi : u ≫ fi = gi) (q : P ⟶ R) (fj : R ⟶ A)
    (h : p ≫ gi = q ≫ fj) (h' : (p ≫ u) ≫ fi = q ≫ fj)
    (M : Modules.{u, u} B S hS A.1 A.2) :
    canonicalComparison p q gi fj h M =
      (modulePullback B S hS p).mapIso (pullbackComparison B S hS u fi gi hgi M) ≪≫
        (pullbackComparison B S hS p u (p ≫ u) rfl ((modulePullback B S hS fi).obj M)).symm ≪≫
        canonicalComparison (p ≫ u) q fi fj h' M := by
  subst hgi
  rw [canonicalComparison_eq, canonicalComparison_eq, pullbackComparison_rfl,
    pullbackComparison_rfl, Functor.mapIso_symm, Iso.symm_symm_eq,
    modulePullback_mapIso_compIso (modulePullbackCompIsoAssoc B S hS) p u fi M]
  simp only [Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_assoc, Iso.symm_self_id_assoc]

/-- Factoring the second leg of a canonical comparison. -/
theorem canonicalComparison_factorRight
    {A P Q R R' : AlgebraicSpaces B S hS} (p : P ⟶ Q) (fi : Q ⟶ A) (q : P ⟶ R)
    (v : R ⟶ R') (fj : R' ⟶ A) (gj : R ⟶ A) (hgj : v ≫ fj = gj)
    (h : p ≫ fi = q ≫ gj) (h' : p ≫ fi = (q ≫ v) ≫ fj)
    (M : Modules.{u, u} B S hS A.1 A.2) :
    canonicalComparison p q fi gj h M =
      canonicalComparison p (q ≫ v) fi fj h' M ≪≫
        pullbackComparison B S hS q v (q ≫ v) rfl ((modulePullback B S hS fj).obj M) ≪≫
        ((modulePullback B S hS q).mapIso
          (pullbackComparison B S hS v fj gj hgj M)).symm := by
  subst hgj
  rw [canonicalComparison_eq, canonicalComparison_eq, pullbackComparison_rfl,
    pullbackComparison_rfl, Functor.mapIso_symm, Iso.symm_symm_eq,
    modulePullback_mapIso_compIso (modulePullbackCompIsoAssoc B S hS) q v fj M]
  simp only [Iso.trans_assoc, Iso.symm_self_id_assoc]

section Family

variable {X Y : AlgebraicSpaces B S hS} {𝒰 : PreZeroHypercover.{v} X}
  {𝒱 : PreZeroHypercover.{v'} Y} {g : X ⟶ Y}

/-- The pulled-back pairwise isomorphism of a canonical descent datum is the canonical
comparison for the two legs composed with the `h₀`. -/
theorem pullbackTransition_canonicalDescentDatum'
    (Φ : 𝒰.HomOver 𝒱 g) (M : Modules.{u, u} B S hS Y.1 Y.2) (hM : M.IsQuasicoherentOnSite)
    (i j : 𝒰.I₀) :
    pullbackTransition B S hS Φ (canonicalDescentDatum' B S hS 𝒱.X 𝒱.f M hM) i j =
      (pullbackComparison B S hS (pairFst B S hS 𝒰.X 𝒰.f i j) (Φ.h₀ i)
          (pairFst B S hS 𝒰.X 𝒰.f i j ≫ Φ.h₀ i) rfl
          ((modulePullback B S hS (𝒱.f (Φ.s₀ i))).obj M)).symm ≪≫
        canonicalComparison (pairFst B S hS 𝒰.X 𝒰.f i j ≫ Φ.h₀ i)
          (pairSnd B S hS 𝒰.X 𝒰.f i j ≫ Φ.h₀ j) (𝒱.f (Φ.s₀ i)) (𝒱.f (Φ.s₀ j))
          (familyPairMap_condition B S hS Φ Φ i j) M ≪≫
        pullbackComparison B S hS (pairSnd B S hS 𝒰.X 𝒰.f i j) (Φ.h₀ j)
          (pairSnd B S hS 𝒰.X 𝒰.f i j ≫ Φ.h₀ j) rfl
          ((modulePullback B S hS (𝒱.f (Φ.s₀ j))).obj M) := by
  have key := transitionOn_canonicalComparison B S hS 𝒱.X 𝒱.f M (Φ.s₀ i) (Φ.s₀ j)
    (familyPairMap B S hS Φ Φ i j) (pairFst B S hS 𝒰.X 𝒰.f i j ≫ Φ.h₀ i)
    (pairSnd B S hS 𝒰.X 𝒰.f i j ≫ Φ.h₀ j) (familyPairMap_fst B S hS Φ Φ i j)
    (familyPairMap_snd B S hS Φ Φ i j)
  rw [pullbackTransition]
  exact congrArg (fun t => (pullbackComparison B S hS (pairFst B S hS 𝒰.X 𝒰.f i j) (Φ.h₀ i)
    (pairFst B S hS 𝒰.X 𝒰.f i j ≫ Φ.h₀ i) rfl
    ((modulePullback B S hS (𝒱.f (Φ.s₀ i))).obj M)).symm ≪≫ t ≪≫
    pullbackComparison B S hS (pairSnd B S hS 𝒰.X 𝒰.f i j) (Φ.h₀ j)
      (pairSnd B S hS 𝒰.X 𝒰.f i j ≫ Φ.h₀ j) rfl
      ((modulePullback B S hS (𝒱.f (Φ.s₀ j))).obj M)) key

/-- **The canonical comparison of the component modules of the pullback of a canonical descent
datum with those of the canonical descent datum of the inverse image commutes with the pairwise
isomorphisms.**  The two component modules at `i` are `(h₀ i)^*(𝒱.f (s₀ i))^*M` and
`(𝒰.f i)^*g^*M`, and the comparison is the canonical comparison of the two inverse images of `M`
along the two legs of the commuting square `Φ.w₀ i` of the morphism of families.

This is the compatibility of
`AlgebraicGeometry.Space.QuasiCoherentDescent.refinementComparison_transition` for a morphism of
families over an arbitrary morphism `g` of the two targets rather than over an identity, and the
comparison it is stated for is a different isomorphism: a comparison of two inverse images of
one module here, a comparison of an inverse image with an iterated one there.

The pairwise isomorphism of the pulled-back datum is written out rather than referred to as
`AlgebraicGeometry.Space.QuasiCoherentDescent.pullbackTransition` at the canonical descent
datum, because the latter carries the `F` field of
`AlgebraicGeometry.Space.QuasiCoherentDescent.canonicalDescentDatum'` in the object arguments of
the composites, and a rewrite inside such a composite leaves a term that is only type-correct up
to a delta-iota step under `CategoryTheory.Iso.trans`, which stops the rewriting; that is the
same obstruction the implementation notes above record.  The identification of the two spellings
is
`AlgebraicGeometry.Space.QuasiCoherentDescent.pullbackTransition_canonicalDescentDatum'` and is
performed where this is consumed. -/
theorem canonicalComparison_pullbackTransition (Φ : 𝒰.HomOver 𝒱 g)
    (M : Modules.{u, u} B S hS Y.1 Y.2) (i j : 𝒰.I₀) :
    (modulePullback B S hS (pairFst B S hS 𝒰.X 𝒰.f i j)).mapIso
          (canonicalComparison (Φ.h₀ i) (𝒰.f i) (𝒱.f (Φ.s₀ i)) g (Φ.w₀ i) M) ≪≫
        canonicalComparison (pairFst B S hS 𝒰.X 𝒰.f i j) (pairSnd B S hS 𝒰.X 𝒰.f i j)
          (𝒰.f i) (𝒰.f j) (pair_condition B S hS 𝒰.X 𝒰.f i j)
          ((modulePullback B S hS g).obj M) =
      ((pullbackComparison B S hS (pairFst B S hS 𝒰.X 𝒰.f i j) (Φ.h₀ i)
              (pairFst B S hS 𝒰.X 𝒰.f i j ≫ Φ.h₀ i) rfl
              ((modulePullback B S hS (𝒱.f (Φ.s₀ i))).obj M)).symm ≪≫
            canonicalComparison (pairFst B S hS 𝒰.X 𝒰.f i j ≫ Φ.h₀ i)
              (pairSnd B S hS 𝒰.X 𝒰.f i j ≫ Φ.h₀ j) (𝒱.f (Φ.s₀ i)) (𝒱.f (Φ.s₀ j))
              (familyPairMap_condition B S hS Φ Φ i j) M ≪≫
            pullbackComparison B S hS (pairSnd B S hS 𝒰.X 𝒰.f i j) (Φ.h₀ j)
              (pairSnd B S hS 𝒰.X 𝒰.f i j ≫ Φ.h₀ j) rfl
              ((modulePullback B S hS (𝒱.f (Φ.s₀ j))).obj M)) ≪≫
        (modulePullback B S hS (pairSnd B S hS 𝒰.X 𝒰.f i j)).mapIso
          (canonicalComparison (Φ.h₀ j) (𝒰.f j) (𝒱.f (Φ.s₀ j)) g (Φ.w₀ j) M) := by
  simp only [canonicalComparison_eq, pullbackComparison_rfl, Functor.mapIso_trans,
    Functor.mapIso_symm, modulePullback_mapIso_compIso (modulePullbackCompIsoAssoc B S hS),
    Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_assoc, Iso.symm_self_id_assoc]
  rw [Iso.subst_trans₃
      (modulePullbackCompIso_eqToIso (pairFst B S hS 𝒰.X 𝒰.f i j) (Φ.w₀ i) M),
    Iso.subst_trans₃
      (modulePullbackCompIso_eqToIso (pairSnd B S hS 𝒰.X 𝒰.f i j) (Φ.w₀ j) M),
    Iso.subst_trans₂
      (modulePullbackCompIso_eqToIso_left (pair_condition B S hS 𝒰.X 𝒰.f i j) g M)]
  simp only [Iso.trans_assoc]
  rw [Iso.subst_trans₂ (eqToIso_trans _ _), Iso.subst_trans₂ (eqToIso_trans _ _)]

/-- **The pullback of the canonical descent datum of a module along a morphism of families is
the canonical descent datum of the inverse image of that module**, as an isomorphism in the
category of descent data of Stacks 04W3.

This is Stacks 04W4 read against Stacks 04W5: for a morphism `Φ : 𝒰.HomOver 𝒱 g` of families
over a morphism `g : X ⟶ Y` of their targets and a quasi-coherent `𝒪_Y`-module `M`, pulling the
canonical descent datum of `M` relative to `𝒱` back along `Φ` gives the canonical descent datum
of `g^*M` relative to `𝒰`.  The comparison of the component modules is the canonical comparison
of the two inverse images of `M` along the two legs of the commuting square of `Φ`, its
compatibility with the pairwise isomorphisms is
`AlgebraicGeometry.Space.QuasiCoherentDescent.canonicalComparison_pullbackTransition`, and the
two are assembled by
`AlgebraicGeometry.Space.QuasiCoherentDescent.DescentDatum.isoMkOfTransitionEq` so that the
compatibility is matched on isomorphisms and not underneath a composite.  Nothing is assumed.

`AlgebraicGeometry.Space.QuasiCoherentDescent.canonicalDescentDatumRefinementIso` is the
statement for a refinement, that is for `g = 𝟙 X`, and neither of the two subsumes the other:
instantiated at `g = 𝟙 X` this compares the pulled-back datum with the canonical descent datum
of `(𝟙 X)^*M`, where that one compares it with the canonical descent datum of `M` itself, and
the two comparisons of the component modules are different isomorphisms. -/
def canonicalDescentDatumPullbackIso (Φ : 𝒰.HomOver 𝒱 g)
    (M : Modules.{u, u} B S hS Y.1 Y.2) (hM : M.IsQuasicoherentOnSite) :
    pullbackDatum B S hS Φ (canonicalDescentDatum' B S hS 𝒱.X 𝒱.f M hM) ≅
      canonicalDescentDatum' B S hS 𝒰.X 𝒰.f ((modulePullback B S hS g).obj M)
        (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS g M hM) :=
  DescentDatum.isoMkOfTransitionEq B S hS
    (fun i => canonicalComparison (Φ.h₀ i) (𝒰.f i) (𝒱.f (Φ.s₀ i)) g (Φ.w₀ i) M)
    (fun i j =>
      (pullbackComparison B S hS (pairFst B S hS 𝒰.X 𝒰.f i j) (Φ.h₀ i)
            (pairFst B S hS 𝒰.X 𝒰.f i j ≫ Φ.h₀ i) rfl
            ((modulePullback B S hS (𝒱.f (Φ.s₀ i))).obj M)).symm ≪≫
          canonicalComparison (pairFst B S hS 𝒰.X 𝒰.f i j ≫ Φ.h₀ i)
            (pairSnd B S hS 𝒰.X 𝒰.f i j ≫ Φ.h₀ j) (𝒱.f (Φ.s₀ i)) (𝒱.f (Φ.s₀ j))
            (familyPairMap_condition B S hS Φ Φ i j) M ≪≫
          pullbackComparison B S hS (pairSnd B S hS 𝒰.X 𝒰.f i j) (Φ.h₀ j)
            (pairSnd B S hS 𝒰.X 𝒰.f i j ≫ Φ.h₀ j) rfl
            ((modulePullback B S hS (𝒱.f (Φ.s₀ j))).obj M))
    (fun i j => canonicalComparison (pairFst B S hS 𝒰.X 𝒰.f i j)
      (pairSnd B S hS 𝒰.X 𝒰.f i j) (𝒰.f i) (𝒰.f j)
      (pair_condition B S hS 𝒰.X 𝒰.f i j) ((modulePullback B S hS g).obj M))
    (fun i j => (pullbackDatum_transition B S hS Φ
        (canonicalDescentDatum' B S hS 𝒱.X 𝒱.f M hM) i j).trans
      (pullbackTransition_canonicalDescentDatum' B S hS Φ M hM i j))
    (canonicalDescentDatum'_transition B S hS 𝒰.X 𝒰.f ((modulePullback B S hS g).obj M)
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS g M hM))
    (canonicalComparison_pullbackTransition B S hS Φ M)

end Family

section Refinement

variable {X : AlgebraicSpaces B S hS} {𝒰 : PreZeroHypercover.{v} X}
  {𝒱 : PreZeroHypercover.{v'} X}

/-- The commuting triangle of a refinement: a member of the refining family maps to a member of
the refined one over the identity of the common target. -/
theorem refinementLeg (Φ : 𝒰.HomOver 𝒱 (𝟙 X)) (i : 𝒰.I₀) :
    Φ.h₀ i ≫ 𝒱.f (Φ.s₀ i) = 𝒰.f i :=
  (Φ.w₀ i).trans (Category.comp_id _)

/-- The comparison of the inverse image of a module along a member of the refining family with
its iterated inverse image through the corresponding member of the refined family. -/
def refinementComparison (Φ : 𝒰.HomOver 𝒱 (𝟙 X)) (M : Modules.{u, u} B S hS X.1 X.2)
    (i : 𝒰.I₀) :
    (modulePullback B S hS (𝒰.f i)).obj M ≅
      (modulePullback B S hS (Φ.h₀ i)).obj
        ((modulePullback B S hS (𝒱.f (Φ.s₀ i))).obj M) :=
  pullbackComparison B S hS (Φ.h₀ i) (𝒱.f (Φ.s₀ i)) (𝒰.f i) (refinementLeg B S hS Φ i) M

/-- **The comparison of a canonical descent datum with the pullback of a canonical descent datum
along a refinement commutes with the pairwise isomorphisms.**  This is the content of Stacks
04W8, steps (1) and (3): the canonical descent datum of a module relative to a refining family
is the pullback along the refinement of its canonical descent datum relative to the refined
family. -/
theorem refinementComparison_transition
    (Φ : 𝒰.HomOver 𝒱 (𝟙 X)) (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) (i j : 𝒰.I₀) :
    (modulePullback B S hS (pairFst B S hS 𝒰.X 𝒰.f i j)).mapIso
          (refinementComparison B S hS Φ M i) ≪≫
        pullbackTransition B S hS Φ (canonicalDescentDatum' B S hS 𝒱.X 𝒱.f M hM) i j =
      canonicalComparison (pairFst B S hS 𝒰.X 𝒰.f i j) (pairSnd B S hS 𝒰.X 𝒰.f i j)
          (𝒰.f i) (𝒰.f j) (pair_condition B S hS 𝒰.X 𝒰.f i j) M ≪≫
        (modulePullback B S hS (pairSnd B S hS 𝒰.X 𝒰.f i j)).mapIso
          (refinementComparison B S hS Φ M j) := by
  rw [pullbackTransition_canonicalDescentDatum' B S hS Φ M hM i j,
    canonicalComparison_factorLeft B S hS (pairFst B S hS 𝒰.X 𝒰.f i j) (Φ.h₀ i)
      (𝒱.f (Φ.s₀ i)) (𝒰.f i) (refinementLeg B S hS Φ i) (pairSnd B S hS 𝒰.X 𝒰.f i j)
      (𝒰.f j) (pair_condition B S hS 𝒰.X 𝒰.f i j)
      (by rw [Category.assoc, refinementLeg B S hS Φ i,
        pair_condition B S hS 𝒰.X 𝒰.f i j]) M,
    canonicalComparison_factorRight B S hS
      (pairFst B S hS 𝒰.X 𝒰.f i j ≫ Φ.h₀ i) (𝒱.f (Φ.s₀ i))
      (pairSnd B S hS 𝒰.X 𝒰.f i j) (Φ.h₀ j) (𝒱.f (Φ.s₀ j)) (𝒰.f j)
      (refinementLeg B S hS Φ j)
      (by rw [Category.assoc, refinementLeg B S hS Φ i,
        pair_condition B S hS 𝒰.X 𝒰.f i j])
      (familyPairMap_condition B S hS Φ Φ i j) M]
  simp only [refinementComparison, Iso.trans_assoc, Iso.trans_refl, Iso.symm_self_id]
  rfl

/-- `AlgebraicGeometry.Space.QuasiCoherentDescent.refinementComparison_transition`, read on
morphisms.  Written out rather than at the projections of the two descent data, so that the
kernel is asked for no reduction here; the reconciliation with the compatibility field of
`AlgebraicGeometry.Space.QuasiCoherentDescent.DescentDatum.Hom` is a projection of a structure
literal and is performed where that field is filled. -/
theorem refinementComparison_naturality
    (Φ : 𝒰.HomOver 𝒱 (𝟙 X)) (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) (i j : 𝒰.I₀) :
    (modulePullback B S hS (pairFst B S hS 𝒰.X 𝒰.f i j)).map
          (refinementComparison B S hS Φ M i).hom ≫
        (pullbackTransition B S hS Φ
          (canonicalDescentDatum' B S hS 𝒱.X 𝒱.f M hM) i j).hom =
      (canonicalComparison (pairFst B S hS 𝒰.X 𝒰.f i j) (pairSnd B S hS 𝒰.X 𝒰.f i j)
          (𝒰.f i) (𝒰.f j) (pair_condition B S hS 𝒰.X 𝒰.f i j) M).hom ≫
        (modulePullback B S hS (pairSnd B S hS 𝒰.X 𝒰.f i j)).map
          (refinementComparison B S hS Φ M j).hom :=
  congrArg Iso.hom (refinementComparison_transition B S hS Φ M hM i j)

/-- The compatibility of the inverse comparisons with the pairwise isomorphisms, read on
morphisms.  This is
`AlgebraicGeometry.Space.QuasiCoherentDescent.refinementComparison_naturality` with the two
comparisons cancelled by `CategoryTheory.Iso.inv_comp_eq_comp_inv_of_comp_eq`, whose four
isomorphisms are supplied by name so that nothing is normalized at these types. -/
theorem refinementComparison_inv_naturality
    (Φ : 𝒰.HomOver 𝒱 (𝟙 X)) (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) (i j : 𝒰.I₀) :
    (modulePullback B S hS (pairFst B S hS 𝒰.X 𝒰.f i j)).map
          (refinementComparison B S hS Φ M i).inv ≫
        (canonicalComparison (pairFst B S hS 𝒰.X 𝒰.f i j) (pairSnd B S hS 𝒰.X 𝒰.f i j)
          (𝒰.f i) (𝒰.f j) (pair_condition B S hS 𝒰.X 𝒰.f i j) M).hom =
      (pullbackTransition B S hS Φ
          (canonicalDescentDatum' B S hS 𝒱.X 𝒱.f M hM) i j).hom ≫
        (modulePullback B S hS (pairSnd B S hS 𝒰.X 𝒰.f i j)).map
          (refinementComparison B S hS Φ M j).inv :=
  Iso.inv_comp_eq_comp_inv_of_comp_eq
    (A := (modulePullback B S hS (pairFst B S hS 𝒰.X 𝒰.f i j)).mapIso
      (refinementComparison B S hS Φ M i))
    (E := pullbackTransition B S hS Φ (canonicalDescentDatum' B S hS 𝒱.X 𝒱.f M hM) i j)
    (D := canonicalComparison (pairFst B S hS 𝒰.X 𝒰.f i j) (pairSnd B S hS 𝒰.X 𝒰.f i j)
      (𝒰.f i) (𝒰.f j) (pair_condition B S hS 𝒰.X 𝒰.f i j) M)
    (G := (modulePullback B S hS (pairSnd B S hS 𝒰.X 𝒰.f i j)).mapIso
      (refinementComparison B S hS Φ M j))
    (refinementComparison_naturality B S hS Φ M hM i j)

/-- **The canonical descent datum of a refining family is the pullback along the refinement of
the canonical descent datum of the refined family**, as an isomorphism of descent data.

This is steps (1) and (3) of the proof of Stacks 04W8 assembled: the comparison of the component
modules is `AlgebraicGeometry.Space.QuasiCoherentDescent.refinementComparison` and its
compatibility with the pairwise isomorphisms of Stacks 04W3 is
`AlgebraicGeometry.Space.QuasiCoherentDescent.refinementComparison_transition`, consumed through
`AlgebraicGeometry.Space.QuasiCoherentDescent.DescentDatum.isoMkOfTransitionEq` so that the
compatibility is matched on isomorphisms and not underneath a composite.  Nothing is assumed: the
associativity coherence of the comparison of inverse images of Stacks 03LU that the compatibility
rests on is `AlgebraicGeometry.Space.modulePullbackCompIsoAssoc`.

The comparison for a morphism of families over an arbitrary morphism of the two targets is
`AlgebraicGeometry.Space.QuasiCoherentDescent.canonicalDescentDatumPullbackIso`; it does not
subsume this one, because at the identity it compares the pulled-back datum with the canonical
descent datum of `(𝟙 X)^*M` rather than with that of `M`. -/
def canonicalDescentDatumRefinementIso (Φ : 𝒰.HomOver 𝒱 (𝟙 X))
    (M : Modules.{u, u} B S hS X.1 X.2) (hM : M.IsQuasicoherentOnSite) :
    canonicalDescentDatum' B S hS 𝒰.X 𝒰.f M hM ≅
      pullbackDatum B S hS Φ (canonicalDescentDatum' B S hS 𝒱.X 𝒱.f M hM) :=
  DescentDatum.isoMkOfTransitionEq B S hS (fun i => refinementComparison B S hS Φ M i)
    (fun i j => canonicalComparison (pairFst B S hS 𝒰.X 𝒰.f i j)
      (pairSnd B S hS 𝒰.X 𝒰.f i j) (𝒰.f i) (𝒰.f j)
      (pair_condition B S hS 𝒰.X 𝒰.f i j) M)
    (fun i j => pullbackTransition B S hS Φ (canonicalDescentDatum' B S hS 𝒱.X 𝒱.f M hM) i j)
    (canonicalDescentDatum'_transition B S hS 𝒰.X 𝒰.f M hM)
    (pullbackDatum_transition B S hS Φ (canonicalDescentDatum' B S hS 𝒱.X 𝒱.f M hM))
    (refinementComparison_transition B S hS Φ M hM)

/-- **The pullback along a refinement of an effective descent datum is effective.**  The easy
half of the refinement transport: the pullback of the canonical descent datum of a module is the
canonical descent datum of that module for the refining family, by
`AlgebraicGeometry.Space.QuasiCoherentDescent.canonicalDescentDatumRefinementIso`. -/
theorem isEffective_pullbackDatum (Φ : 𝒰.HomOver 𝒱 (𝟙 X))
    {D : DescentDatum B S hS 𝒱.X 𝒱.f} (hD : IsEffective B S hS 𝒱.X 𝒱.f D) :
    IsEffective B S hS 𝒰.X 𝒰.f (pullbackDatum B S hS Φ D) := by
  obtain ⟨M, hM, ⟨e⟩⟩ := hD
  exact ⟨M, hM, ⟨(pullbackFunctor B S hS Φ).mapIso e ≪≫
    (canonicalDescentDatumRefinementIso B S hS Φ M hM).symm⟩⟩

/-- **Effectivity descends from a refinement.**  If the pullback along a refinement `Φ : 𝒰 ⟶ 𝒱`
of a descent datum for `𝒱` is effective and pullback along `Φ` is fully faithful, then the datum
itself is effective.

The pullback of the datum is isomorphic to the canonical descent datum of a module `M` for the
refining family, hence — by
`AlgebraicGeometry.Space.QuasiCoherentDescent.canonicalDescentDatumRefinementIso` — to the
pullback of the canonical descent datum of `M` for the refined family; full faithfulness carries
that isomorphism back across the pullback functor.

Full faithfulness of pullback along a refinement is where descent of *morphisms* enters, and it
is the only input: nothing is assumed about either family. -/
theorem isEffective_of_isEffective_pullbackDatum (Φ : 𝒰.HomOver 𝒱 (𝟙 X))
    (hff : (pullbackFunctor B S hS Φ).FullyFaithful)
    {D : DescentDatum B S hS 𝒱.X 𝒱.f}
    (hD : IsEffective B S hS 𝒰.X 𝒰.f (pullbackDatum B S hS Φ D)) :
    IsEffective B S hS 𝒱.X 𝒱.f D := by
  obtain ⟨M, hM, ⟨e⟩⟩ := hD
  exact ⟨M, hM, ⟨hff.preimageIso (e ≪≫ canonicalDescentDatumRefinementIso B S hS Φ M hM)⟩⟩

/-- Along a refinement whose pullback functor is fully faithful, a descent datum is effective
exactly when its pullback is. -/
theorem isEffective_pullbackDatum_iff (Φ : 𝒰.HomOver 𝒱 (𝟙 X))
    (hff : (pullbackFunctor B S hS Φ).FullyFaithful)
    {D : DescentDatum B S hS 𝒱.X 𝒱.f} :
    IsEffective B S hS 𝒰.X 𝒰.f (pullbackDatum B S hS Φ D) ↔
      IsEffective B S hS 𝒱.X 𝒱.f D :=
  ⟨isEffective_of_isEffective_pullbackDatum B S hS Φ hff,
    isEffective_pullbackDatum B S hS Φ⟩

/-- **Effectivity for a family follows from effectivity for any refinement of it whose pullback
functor is fully faithful.**  This is the form the reduction of Stacks 04W8 to a covering by
schemes consumes: an arbitrary family is refined by one whose members are schemes
(`AlgebraicGeometry.Space.exists_fpqc_scheme_refinement`, Stacks 0419), effectivity is proved for
the refinement, and this carries it back. -/
theorem isEffective_of_forall_isEffective (Φ : 𝒰.HomOver 𝒱 (𝟙 X))
    (hff : (pullbackFunctor B S hS Φ).FullyFaithful)
    (h : ∀ E : DescentDatum B S hS 𝒰.X 𝒰.f, IsEffective B S hS 𝒰.X 𝒰.f E)
    (D : DescentDatum B S hS 𝒱.X 𝒱.f) : IsEffective B S hS 𝒱.X 𝒱.f D :=
  isEffective_of_isEffective_pullbackDatum B S hS Φ hff (h _)

end Refinement

end AlgebraicGeometry.Space.QuasiCoherentDescent

end
