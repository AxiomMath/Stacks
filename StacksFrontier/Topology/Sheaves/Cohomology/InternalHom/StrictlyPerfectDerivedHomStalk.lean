module

public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.StrictlyPerfectHomComplexStalkIso
public import StacksFrontier.Homology.HomComplex.RingEquivTransport
public import StacksFrontier.Homology.HomComplex.ProjectiveRHom
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedStalk.StalkwiseIsomorphism
public import StacksFrontier.Topology.Sheaves.Modules.StalkTensor
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFreeRetract
public import StacksFrontier.AlgebraicGeometry.Cohomology.GlobalGeneration.Stalks
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalTypesUnderComparison

/-!
# The stalk of the derived internal Hom out of a strictly perfect complex

Let `Rc` be a sheaf of commutative rings on a topological space `X`, write `O_X` for the
underlying sheaf of rings, let `x ∈ X` and write `A = O_{X,x}` for the stalk ring. **Stacks
Tag 0GM8, case (1)** says that for `E` a perfect complex of `O_X`-modules and `F` arbitrary the
derived internal Hom commutes with taking the stalk at `x`:

`RSheafHom_{O_X}(E, F)_x ≅ RHom_A(E_x, F_x)` in `D(A)`.

This file proves that isomorphism in two forms. The first,
`derivedStalkDerivedSheafHomIsoNearPoint`, is **germ-local**: `E` is bounded and each of its terms
is a direct summand of a finite free module on *one open neighbourhood `V` of `x`*, with no
hypothesis at all on `E` away from `V`. The second,
`derivedStalkDerivedSheafHomIso`, assumes `E` **strictly perfect** on all of `X` and takes the
shorter route through Tag 08DM. Both are isomorphisms of objects of `D(A)`, not the
canonical comparison map of Tag 08I3 — the canonical-map version is
`Stacks.Cohomology.DerivedInternalHomStalk.stalkSheafHomMap` and is blocked on Tag 0GM7 together
with an unconstructed `StalkPresentation`; see the implementation notes of
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomStalk`. What is built here
instead is a chain of model computations, each of which is already available, and the resulting
isomorphism is stated at exactly the two spellings Tag 0G02 consumes.

## The chain

1. **A model for the left-hand side.** Globally this is Stacks 08DM,
   `strictlyPerfectHomComparison_isIso`: for `E` strictly perfect the class of the *ordinary*
   internal Hom complex `SheafHom(E, F)` is `RSheafHom(E, F)`, with no hypothesis on `F`.
   Germ-locally that is unavailable — with the hypothesis supported only near `x` the comparison
   need not be invertible — and its place is taken by the K-injective model
   `derivedSheafHomComparison`, which represents `RSheafHom(E, I)` by `SheafHom(E, I)` for
   K-injective `I` with **no hypothesis on `E`**, after replacing `F` by its K-injective
   resolution.
2. **The stalk functor is exact**, so `AlgebraicGeometry.SheafOfModules.derivedStalkFunctor` is
   induced by taking stalks degreewise: `derivedStalkFunctorFactors` turns the derived stalk of a
   class `Q C` into the class of the complex of stalks of `C`.
3. **The stalk of the internal Hom complex**, Stacks 01CP assembled degreewise:
   `isIso_sheafHomComplexStalkChainMap` identifies `SheafHom(E, F)_x` with the naive Hom complex
   of the complexes of stalks. That comparison is a map of complexes of *abelian groups*; the
   first half of this file upgrades it to a map of complexes of `A`-modules.
4. **The Hom complex over a ring computes `RHom`**, Stacks 0A66,
   `StacksDraft.DerivedHom.projectiveHomComparison`: the stalk of a finite free summand is a
   projective `A`-module and boundedness of `E` bounds the complex of stalks above, so the Hom
   complex of the complexes of stalks computes `RHom_A`.

## Main definitions

* `StacksDraft.DerivedHom.projectiveHomModelIsoOverRing`: **Stacks 0A66 at the bundle of
  Tag 0A63.** For `P` bounded above with projective terms and `L` arbitrary,
  `RHom_A(P, L) ≅ Q(Hom^•_A(P, L))` with `RHom` taken in the bundle
  `StacksDraft.DerivedHom.derivedHomAdjunctionOverRing`, which is the spelling every statement
  about the local rings of a ringed space is written in.
* `Stacks.SheafOfModules.DerivedHomStalk.stalkCochainMap`,
  `…stalkHomComplexChainMap`, `…stalkHomComplexIso`: the comparison of step 3 as a morphism, and
  then an isomorphism, of complexes of modules over the `CommRingCat`-valued stalk ring.
* `Stacks.SheafOfModules.DerivedHomStalk.stalkRelabelIso`,
  `…stalkComplexRelabelIso`: the identification of the two spellings of the stalk of a sheaf of
  modules — over the `CommRingCat`-valued stalk ring and over the `RingCat`-valued one that
  `stalkFunctor` uses.
* `Stacks.SheafOfModules.DerivedHomStalk.stalkHomComplexIsoOverStalkRing`: step 3 over the
  `RingCat`-valued stalk ring, which is the ring `RHom` is taken over.
* `Stacks.SheafOfModules.DerivedHomStalk.stalkMapOfOver`: the stalk at `x` of a homomorphism of
  `O_X`-modules defined only over an open neighbourhood of `x`, functorial in that homomorphism.
  This is `Stacks.SheafOfModules.SheafHomStalk.stalkLinearMap` read over the `RingCat`-valued
  stalk ring.

## Main results

* `Stacks.SheafOfModules.DerivedHomStalk.homComplexStalkCochainMap_smul`: the degree-`n` stalk
  comparison of Stacks 01CP is linear over the stalk ring. This is what makes step 3 a statement
  about complexes of modules rather than of abelian groups, and it is read off the agreement
  `homComplexStalkCochainMap_v`: the comparison is computed by the stalk maps of the degree
  projections through Stacks 01CP at each term, and both of those are linear.
* `Stacks.SheafOfModules.DerivedHomStalk.projective_stalk_of_isFiniteFreeSummand`: **the stalk of
  a direct summand of a finite free module is a projective module.** The stalk functor is
  additive, so it carries the retraction onto `O_X^{⊕r}` to a retraction onto `A^{⊕r}`.
* `Stacks.SheafOfModules.DerivedHomStalk.projective_stalk_of_retract_over`: **the germ-local
  form of the same statement.** If `M` is a retract of `N` only over an open neighbourhood `V` of
  `x` and the stalk of `N` is projective, then the stalk of `M` is projective. The retraction over
  `V` is carried to the stalks by `Stacks.SheafOfModules.DerivedHomStalk.stalkMapOfOver`, the
  stalk at `x` of a homomorphism defined only over `V`.
* `Stacks.SheafOfModules.DerivedHomStalk.isStrictlyLE_stalkComplex`: boundedness of `E` bounds
  the complex of stalks above.
* In `Stacks.SheafOfModules.DerivedHomStalk`,
  `nonempty_localPresentation_of_isDirectSummandOfFiniteFree_over` and
  `bijective_sheafHomStalkLinearMap_of_isDirectSummandOfFiniteFree_over`: **Stacks 01CP for a
  source which is a finite free summand only near `x`.** The retraction over `V` gives a finite
  presentation of `M|_V`, hence local presentation data for `M` at `x`, which is all that
  `Stacks.SheafOfModules.SheafHomStalk.bijective_sheafHomStalkLinearMap_of_localPresentation`
  needs.
* `Stacks.SheafOfModules.DerivedHomStalk.derivedStalkDerivedSheafHomIsoNearPoint`: **Tag 0GM8
  case (1) for a source strictly perfect near `x`**, the isomorphism
  `RSheafHom(E, F)_x ≅ RHom_A(E_x, F_x)` under the germ-local hypothesis.
* `Stacks.SheafOfModules.DerivedHomStalk.derivedStalkDerivedSheafHomIso`: **Tag 0GM8 case (1) for
  a strictly perfect source**, the same isomorphism via Tag 08DM.

## Implementation notes

**Two stalk rings.** `AlgebraicGeometry.SheafOfModules.stalkFunctor`, hence
`derivedStalkFunctor`, takes its modules over the `RingCat`-valued stalk of
`Rc ⋙ forget₂ CommRingCat RingCat`, while the internal-Hom stalk development
(`Stacks.SheafOfModules.SheafHomStalk`) is written over the `CommRingCat`-valued stalk
`ringStalk Rc x` of `Rc` itself. These are two different types — two colimits taken in two
categories — with the same underlying abelian group, and the comparison is
`SemilinearStalk.commStalkRingEquiv`. The crossing is confined to two declarations:
`stalkRelabelIso`, which is the identity map read as an isomorphism of modules over the
`RingCat`-valued stalk (its `map_smul'` is
`AlgebraicGeometry.SheafOfModules.commStalkRingEquiv_smul_eq'`), and
`stalkComplexRelabelIso`, which assembles it degreewise. Everything else is moved across by
`StacksDraft.ScalarTransport.relabel` and its two transport isomorphisms,
`StacksDraft.ScalarTransport.homComplexRelabelIso` and
`StacksDraft.ScalarTransport.homComplexRCongr`.

**Why `projectiveHomModelIsoOverRing` has to be built here.** Stacks 0A66 is available as
`StacksDraft.DerivedHom.projectiveHomComparison`, whose `iso` field is stated for
`StacksDraft.DerivedHom.derivedHomAdjunction`, the tensor–Hom bundle at a *fixed* module
universe. The spelling the local-duality statements use is
`StacksDraft.DerivedHom.derivedHomAdjunctionOverRing`, which is by construction that bundle over
`ULift.{v} A` transported along `derivedScalarEquivalence`; no `rfl` collapses the two, even when
the module universe equals the ring universe. The bridge is assembled from
`derivedHomULiftIso`, the `ULift` form `projectiveHomComparisonULift` of Stacks 0A66, and
`StacksDraft.ScalarTransport.homComplexRelabelIso` to move the Hom complex back across the
scalar relabelling — the same shape as the K-injective bridges that
`StacksFrontier.RingTheory.Dualizing.NormalizedFiniteLengthQuotient` and
`StacksFrontier.RingTheory.Dualizing.LocalCohomology.NormalizedDualizingComplex` each carry
privately, with the K-injective target hypothesis replaced by a bounded-above projective source.

**How the germ-local form is obtained, and what had to be generalized.** Tag 0GM8 is a statement
about the stalk at one point, so the natural hypothesis is the germ-local one. Three of the four
steps were already germ-local, or became so here:

* step 1 is replaced by the K-injective model, which needs nothing of `E`;
* step 3's only use of the termwise hypothesis is Stacks 01CP at each term, and the proof of Stacks
  01CP in `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomStalk` was *already* a germ-local
  argument — its two halves consumed their finiteness instance in a single line, only to produce
  `Stacks.SheafOfModules.LocalGenerators` resp. `Stacks.SheafOfModules.LocalPresentation` data on a
  neighbourhood of `x`. Those two theorems, and the degreewise statements of
  `StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.StrictlyPerfectHomComplexStalkIso` that
  consume them, have been restated with that data as a hypothesis and their original forms
  re-derived from the general ones;
* step 4 needs the stalk at `x` only, and `projective_stalk_of_retract_over` uses the retraction
  only through its image under the stalk functor.

The germ-local hypothesis is phrased as a retraction onto a finite free module over `V`, which is
the termwise condition of Stacks 08FL read on the slice over `V`. It is *not* stated with
`AlgebraicGeometry.RingedSite.IsFiniteFreeSummand ((ringedSite Rc).over V)`: that spelling names
the finite free module as an iterated binary biproduct in the slice category, and identifying it
with the restriction of the global `O_X^{⊕r}` needs finite biproducts on the slice site, whose
instances are not available here. The free spelling needs only
`Stacks.Sheaves.GlobalTypeComparison.mapFreeIso` (`freeOverIso`), and it is also the spelling in
which Stacks 08FL states its termwise condition.

The global form `derivedStalkDerivedSheafHomIso` is kept and proved through Tag 08DM rather than
derived from the germ-local one at `V = ⊤`: `SheafOfModules.overFunctor _ ⊤` is not the identity
functor on the nose, so the global termwise hypothesis is not literally an instance of the
germ-local one, and the 08DM route avoids the K-injective resolution altogether.

## References

* [Stacks Project, Tag 01CP](https://stacks.math.columbia.edu/tag/01CP)
* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0A66](https://stacks.math.columbia.edu/tag/0A66)
* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
* [Stacks Project, Tag 08DM](https://stacks.math.columbia.edu/tag/08DM)
* [Stacks Project, Tag 0G02](https://stacks.math.columbia.edu/tag/0G02)
* [Stacks Project, Tag 0GM8](https://stacks.math.columbia.edu/tag/0GM8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry CochainComplex.HomComplex
open Stacks.SheafOfModules.SheafHomStalk

attribute [local instance_reducible] CategoryTheory.sheafCompose

universe u

namespace StacksDraft.DerivedHom

attribute [local instance] HasDerivedCategory.standard

/-! ### Stacks 0A66 at the tensor–Hom bundle of Stacks 0A63 -/

section ProjectiveBridge

variable (A : Type u) [CommRing A]

/-- **Stacks 0A66 for the bundle of Stacks 0A63.** For `P` a complex of `A`-modules bounded above
with projective terms and `L` arbitrary, the derived internal Hom `RHom_A(P, L)` — taken in
`StacksDraft.DerivedHom.derivedHomAdjunctionOverRing`, the bundle every statement about the local
rings of a ringed space is written in — is the class of the ordinary Hom complex
`Hom^•_A(P, L)`.

`StacksDraft.DerivedHom.projectiveHomComparison` is Stacks 0A66 for
`StacksDraft.DerivedHom.derivedHomAdjunction`, the bundle at a fixed module universe, and the
bundle over the ring is that one over `ULift A` conjugated by restriction of scalars. So the
statement is transported across the conjugation: `derivedHomULiftIso` moves the internal Hom,
`StacksDraft.ScalarTransport.homComplexRelabelIso` moves the Hom complex, and the two
hypotheses on `P` are carried to `ULift A` by
`CochainComplex.isStrictlyLE_mapHomologicalComplex_obj_iff` and by restriction of scalars along
a ring isomorphism being an equivalence, hence preserving projective objects. -/
def projectiveHomModelIsoOverRing
    (P L : CochainComplex (ModuleCat.{u} A) ℤ) (d : ℤ)
    [P.IsStrictlyLE d] [∀ i, Projective (P.X i)] :
    (derivedHomAdjunctionOverRing.{u, 0, u + 1} A).hom.obj
        (Opposite.op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj L) ≅
      DerivedCategory.Q.obj (CochainComplex.HomComplexR A P L) := by
  let m := uliftModuleEquivalence.{u, u, 0} A
  let e := derivedScalarEquivalence.{u, 0, u + 1} A
  let mc := m.mapHomologicalComplex (ComplexShape.up ℤ)
  let P' := mc.inverse.obj P
  let L' := mc.inverse.obj L
  haveI : CochainComplex.IsStrictlyLE P' d :=
    (CochainComplex.isStrictlyLE_mapHomologicalComplex_obj_iff P m.inverse d).2 inferInstance
  haveI : ∀ i, Projective (P'.X i) := fun i =>
    m.inverse.projective_obj_of_projective inferInstance
  let bP : e.functor.obj (DerivedCategory.Q.obj P') ≅ DerivedCategory.Q.obj P :=
    m.functor.mapDerivedCategoryFactors.app P' ≪≫
      DerivedCategory.Q.mapIso (mc.counitIso.app P)
  let bL : e.functor.obj (DerivedCategory.Q.obj L') ≅ DerivedCategory.Q.obj L :=
    m.functor.mapDerivedCategoryFactors.app L' ≪≫
      DerivedCategory.Q.mapIso (mc.counitIso.app L)
  exact (derivedHomAdjunctionOverRing.{u, 0, u + 1} A).hom.mapIso (bP.op.prod bL.symm) ≪≫
    (derivedHomULiftIso.{u, 0, u + 1} A).app
        (Opposite.op (DerivedCategory.Q.obj P'), DerivedCategory.Q.obj L') ≪≫
    e.functor.mapIso ((projectiveHomComparison (R := ULift.{0} A)).iso P' L' d) ≪≫
    m.functor.mapDerivedCategoryFactors.app
      (CochainComplex.HomComplexR (ULift.{0} A) P' L') ≪≫
    DerivedCategory.Q.mapIso (StacksDraft.ScalarTransport.homComplexRelabelIso
      (ULift.ringEquiv : ULift.{0} A ≃+* A) P' L')

end ProjectiveBridge

end StacksDraft.DerivedHom

namespace Stacks.SheafOfModules.DerivedHomStalk

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ T : Opens X, HasSheafify ((Opens.grothendieckTopology X).over T) AddCommGrpCat.{u}]
  [∀ T : Opens X, ((Opens.grothendieckTopology X).over T).WEqualsLocallyBijective
    AddCommGrpCat.{u}]
  (E F : CochainComplex (StructureSheafModules Rc) ℤ)
  (hE : {i : ℤ | ¬ IsZero (E.X i)}.Finite)
  (hterm : ∀ i : ℤ, RingedSite.IsFiniteFreeSummand (ringedSite Rc) (E.X i))
  (x : X)

/-! ### The stalk comparison as a map of complexes of modules -/

/-- The canonical internal Hom complex `SheafHom(E, F)` of Stacks 0A8Z, read as a realization of
the internal Hom complex in the sense of
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.Defs`. This is the realization every
statement below is taken at, and the one `sheafHomComplexStalkChainMap` is defined from. -/
abbrev homComplex : SheafHomComplex Rc E F :=
  ofSite Rc E F (RingedSite.sheafHomComplex (ringedSite Rc) E F)

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ T : Opens X, HasSheafify ((Opens.grothendieckTopology X).over T) AddCommGrpCat.{u}]
    [∀ T : Opens X, ((Opens.grothendieckTopology X).over T).WEqualsLocallyBijective
      AddCommGrpCat.{u}] in
/-- **The degree-`n` stalk comparison is linear over the stalk ring.** The comparison
`homComplexStalkCochainMap` from the stalk at `x` of the degree-`n` term of `SheafHom(E, F)` to
the degree-`n` term of the naive Hom complex of the complexes of stalks is built as a map of
abelian groups, by a colimit descent; this records that it is `O_{X,x}`-linear.

**There is no hypothesis on `E` or `F`.** The proof is the agreement
`homComplexStalkCochainMap_v_canonical`: the `(-q, n-q)` component of the comparison is the image
under the canonical map of Stacks 01CP at the `q`-th term of the stalk map of the `q`-th degree
projection, and both of those are linear. Invertibility of Stacks 01CP is not needed to see that
the comparison is linear, only to see that it is bijective. -/
lemma homComplexStalkCochainMap_smul (n : ℤ) (r : ringStalk Rc x)
    (t : modStalk ((RingedSite.sheafHomComplex (ringedSite Rc) E F).obj.X n) x) :
    SheafHomStalk.homComplexStalkCochainMap (homComplex Rc E F) n x (r • t) =
      r • SheafHomStalk.homComplexStalkCochainMap (homComplex Rc E F) n x t := by
  refine SheafHomStalk.cochain_ext_neg fun q => ?_
  -- The two `map_smul`s and the scalar multiple of a cochain are taken as equations rather than
  -- by `rw`: the internal Hom sheaf named through `internalHomSheafHom` is not type-correct at
  -- `implicit` transparency, so no motive can be built in the goal.
  have hsmul : ∀ z, (r • SheafHomStalk.homComplexStalkCochainMap (homComplex Rc E F) n x z).v
        (-q) (n - q) (by omega)
      = r • (SheafHomStalk.homComplexStalkCochainMap (homComplex Rc E F) n x z).v
        (-q) (n - q) (by omega) := fun z => by rw [Cochain.smul_v]
  refine (homComplexStalkCochainMap_v_canonical Rc E F n x q (r • t)).trans ?_
  refine Eq.trans ?_ (hsmul t).symm
  refine Eq.trans ?_ (congrArg (fun y => r • y)
    (homComplexStalkCochainMap_v_canonical Rc E F n x q t)).symm
  exact congrArg ModuleCat.ofHom
    ((congrArg (sheafHomStalkLinearMap (internalHomSheafHom Rc (E.X (-q)) (F.X (n - q))) x)
        (map_smul (modStalkMap (RingedSite.homDegreeProjection (ringedSite Rc) E F n q) x)
          r t)).trans
      (map_smul (sheafHomStalkLinearMap (internalHomSheafHom Rc (E.X (-q)) (F.X (n - q))) x) r _))

/-- The degree-`n` stalk comparison as a morphism of `O_{X,x}`-modules: the underlying map is
`homComplexStalkCochainMap`, and linearity is `homComplexStalkCochainMap_smul`. The target is the
degree-`n` term of the `O_{X,x}`-linear Hom complex `CochainComplex.HomComplexR`, whose terms are
the same cochain groups as those of `CochainComplex.HomComplex` with their module structure
recorded. No hypothesis on `E` or `F`. -/
def stalkCochainMap (n : ℤ) :
    (modStalkComplex (RingedSite.sheafHomComplex (ringedSite Rc) E F).obj x).X n ⟶
      (CochainComplex.HomComplexR (ringStalk Rc x) (modStalkComplex E x)
        (modStalkComplex F x)).X n :=
  ModuleCat.ofHom
    { toFun := fun t => SheafHomStalk.homComplexStalkCochainMap (homComplex Rc E F) n x t
      map_add' := fun t t' => map_add _ t t'
      map_smul' := fun r t => homComplexStalkCochainMap_smul Rc E F x n r t }

/-- The stalk comparison as a morphism of complexes of `O_{X,x}`-modules. That the degreewise
maps commute with the differentials is already known of the underlying maps of abelian groups —
it is the `comm` field of `sheafHomComplexStalkChainMap` — and the forgetful functor to abelian
groups is faithful, so the same equation holds here. No hypothesis on `E` or `F`. -/
def stalkHomComplexChainMap :
    modStalkComplex (RingedSite.sheafHomComplex (ringedSite Rc) E F).obj x ⟶
      CochainComplex.HomComplexR (ringStalk Rc x) (modStalkComplex E x)
        (modStalkComplex F x) where
  f n := stalkCochainMap Rc E F x n
  comm' n m _ := by
    refine ModuleCat.hom_ext <| LinearMap.ext fun t => ?_
    exact ConcreteCategory.congr_hom ((sheafHomComplexStalkChainMap Rc E F x).comm n m) t

include hE in
/-- **The stalk of the internal Hom complex is the Hom complex of the stalks, over the stalk
ring.** For `E` bounded and `F` arbitrary,

`SheafHom(E, F)_x ≅ Hom^•_{O_{X,x}}(E_x, F_x)`

as complexes of `O_{X,x}`-modules, as soon as the canonical map of Stacks 01CP is bijective at
each pair of terms. This is
`Stacks.SheafOfModules.isIso_sheafHomComplexStalkChainMap_of_bijective` with the module structures
retained; the degreewise maps are bijective by
`bijective_homComplexStalkCochainMap_of_bijective`.

The hypothesis `h01` is about the single stalk at `x`, so this applies to a complex which is
strictly perfect only near `x`. -/
def stalkHomComplexIso
    (h01 : ∀ i j : ℤ, Function.Bijective
      (sheafHomStalkLinearMap (internalHomSheafHom Rc (E.X i) (F.X j)) x)) :
    modStalkComplex (RingedSite.sheafHomComplex (ringedSite Rc) E F).obj x ≅
      CochainComplex.HomComplexR (ringStalk Rc x) (modStalkComplex E x)
        (modStalkComplex F x) := by
  haveI : ∀ n : ℤ, IsIso ((stalkHomComplexChainMap Rc E F x).f n) := fun n =>
    (ConcreteCategory.isIso_iff_bijective _).2
      (bijective_homComplexStalkCochainMap_of_bijective Rc E F hE n x h01)
  haveI := HomologicalComplex.Hom.isIso_of_components (stalkHomComplexChainMap Rc E F x)
  exact asIso (stalkHomComplexChainMap Rc E F x)

/-! ### Crossing between the two spellings of the stalk ring -/

/-- The stalk ring `O_{X,x}` in the spelling `AlgebraicGeometry.SheafOfModules.stalkFunctor`
produces: the `RingCat`-valued stalk at `x` of the sheaf of rings underlying `Rc`. -/
abbrev stalkRing : Type u :=
  TopCat.Presheaf.stalk (C := RingCat.{u}) (structureSheaf Rc).obj x

/-- The stalk ring is commutative. The `RingCat`-valued stalk carries only a `Ring` instance of
its own; the commutativity is transported from the `CommRingCat`-valued stalk along
`SemilinearStalk.commStalkRingEquiv`. It is registered as a *local* instance, as in
`StacksFrontier.Topology.Sheaves.Modules.StalkTensor`, whose implementation notes record why a copy
keyed on this spelling cannot be registered globally. -/
abbrev stalkCommRing : CommRing (stalkRing Rc x) :=
  StacksDraft.StalkTensor.commRing_stalk Rc.obj x

attribute [local instance] stalkCommRing

/-- Reading an `O_{X,x}`-module over the `CommRingCat`-valued stalk ring as one over the
`RingCat`-valued stalk ring: restriction of scalars along
`SemilinearStalk.commStalkRingEquiv`. The underlying abelian group is unchanged. -/
abbrev relabelStalk : ModuleCat.{u} (ringStalk Rc x) ⥤ ModuleCat.{u} (stalkRing Rc x) :=
  StacksDraft.ScalarTransport.relabel
    (SemilinearStalk.commStalkRingEquiv Rc.obj x).symm

/-- **The two module structures on the stalk of a sheaf of modules agree.** The stalk of `M` as a
module over the `CommRingCat`-valued stalk ring, relabelled along
`SemilinearStalk.commStalkRingEquiv`, is the stalk of `M` as `stalkFunctor` produces it. Both
sides have the same underlying abelian group and the identity map is linear, which is
`AlgebraicGeometry.SheafOfModules.commStalkRingEquiv_smul_eq'`. -/
def stalkRelabelIso (M : StructureSheafModules Rc) :
    (relabelStalk Rc x).obj (ModuleCat.of (ringStalk Rc x) (modStalk M x)) ≅
      (AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheaf Rc) x).obj M where
  hom := ConcreteCategory.ofHom (C := ModuleCat.{u} (stalkRing Rc x))
    { toFun := fun m => m
      map_add' := fun _ _ => rfl
      map_smul' := fun a m =>
        AlgebraicGeometry.SheafOfModules.commStalkRingEquiv_smul_eq' Rc x M.val a m }
  inv := ConcreteCategory.ofHom (C := ModuleCat.{u} (stalkRing Rc x))
    { toFun := fun m => m
      map_add' := fun _ _ => rfl
      map_smul' := fun a m =>
        (AlgebraicGeometry.SheafOfModules.commStalkRingEquiv_smul_eq' Rc x M.val a m).symm }

/-- The complex of stalks of a complex of `O_X`-modules, as `stalkFunctor` produces it. -/
abbrev stalkComplex (K : CochainComplex (StructureSheafModules Rc) ℤ) :
    CochainComplex (ModuleCat.{u} (stalkRing Rc x)) ℤ :=
  ((AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheaf Rc) x).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj K

/-- `stalkRelabelIso` degreewise: the complex of stalks in the `modStalk` spelling, relabelled, is
the complex of stalks that `stalkFunctor` produces. The differentials agree because the stalk map
of a morphism agrees in the two spellings, which is `modStalkMap_eq_stalkFunctor_map`. -/
def stalkComplexRelabelIso (K : CochainComplex (StructureSheafModules Rc) ℤ) :
    (StacksDraft.ScalarTransport.relabelComplex
        (SemilinearStalk.commStalkRingEquiv Rc.obj x).symm).obj (modStalkComplex K x) ≅
      stalkComplex Rc x K :=
  HomologicalComplex.Hom.isoOfComponents (fun n => stalkRelabelIso Rc x (K.X n))
    (fun n m _ => by
      refine ModuleCat.hom_ext <| LinearMap.ext fun t => ?_
      exact (modStalkMap_eq_stalkFunctor_map (K.d n m) x t).symm)

include hE in
/-- **The stalk of the internal Hom complex is the Hom complex of the stalks**, over the
`RingCat`-valued stalk ring that the derived stalk functor takes its modules over.

This is `stalkHomComplexIso` carried across the relabelling: the relabelling is applied to the
whole isomorphism, `StacksDraft.ScalarTransport.homComplexRelabelIso` moves it past the Hom
complex, and `StacksDraft.ScalarTransport.homComplexRCongr` puts the two arguments back in the
`stalkFunctor` spelling. -/
def stalkHomComplexIsoOverStalkRing
    (h01 : ∀ i j : ℤ, Function.Bijective
      (sheafHomStalkLinearMap (internalHomSheafHom Rc (E.X i) (F.X j)) x)) :
    stalkComplex Rc x (RingedSite.sheafHomComplex (ringedSite Rc) E F).obj ≅
      CochainComplex.HomComplexR (stalkRing Rc x) (stalkComplex Rc x E)
        (stalkComplex Rc x F) :=
  (stalkComplexRelabelIso Rc x (RingedSite.sheafHomComplex (ringedSite Rc) E F).obj).symm ≪≫
    (StacksDraft.ScalarTransport.relabelComplex
        (SemilinearStalk.commStalkRingEquiv Rc.obj x).symm).mapIso
      (stalkHomComplexIso Rc E F hE x h01) ≪≫
    StacksDraft.ScalarTransport.homComplexRelabelIso
      (SemilinearStalk.commStalkRingEquiv Rc.obj x).symm _ _ ≪≫
    StacksDraft.ScalarTransport.homComplexRCongr (R := stalkRing Rc x)
      (C := ModuleCat.{u} (stalkRing Rc x))
      (stalkComplexRelabelIso Rc x E) (stalkComplexRelabelIso Rc x F)

/-! ### The stalk of a strictly perfect term is a projective module -/

section Projectivity

attribute [local instance] AlgebraicGeometry.RingedSite.hasFiniteBiproducts_sheafOfModules

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ T : Opens X, HasSheafify ((Opens.grothendieckTopology X).over T) AddCommGrpCat.{u}]
    [∀ T : Opens X, ((Opens.grothendieckTopology X).over T).WEqualsLocallyBijective
      AddCommGrpCat.{u}] in
/-- The stalk of the structure sheaf, regarded as a module over itself, is a projective module:
it is `O_{X,x}` over itself, by `AlgebraicGeometry.stalkUnitLinearEquiv`. -/
lemma projective_stalk_unit :
    Projective ((AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheaf Rc) x).obj
      (_root_.SheafOfModules.unit (structureSheaf Rc))) := by
  have : Projective (ModuleCat.of (stalkRing Rc x) (stalkRing Rc x)) := inferInstance
  exact Projective.of_iso
    (AlgebraicGeometry.stalkUnitLinearEquiv (structureSheaf Rc) x).toModuleIso.symm inferInstance

omit [∀ T : Opens X, HasSheafify ((Opens.grothendieckTopology X).over T) AddCommGrpCat.{u}]
    [∀ T : Opens X, ((Opens.grothendieckTopology X).over T).WEqualsLocallyBijective
      AddCommGrpCat.{u}] in
/-- The stalk of `O_X^{⊕r}` is a projective module. `AlgebraicGeometry.RingedSite.unitPower` is
an iterated binary biproduct, so this is an induction on `r`: the stalk functor is additive, so
it carries the zero object to a zero object and a binary biproduct to a binary biproduct. -/
lemma projective_stalk_unitPower (r : ℕ) :
    Projective ((AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheaf Rc) x).obj
      (RingedSite.unitPower (ringedSite Rc) r)) := by
  have := AlgebraicGeometry.SheafOfModules.stalkFunctor_additive (structureSheaf Rc) x
  have := Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts
    (AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheaf Rc) x)
  induction r with
  | zero =>
    exact (Functor.map_isZero _ (Limits.isZero_zero _)).projective
  | succ r ih =>
    have := ih
    have := projective_stalk_unit Rc x
    -- `unitPower` is an object of `SheafOfModules (Tensor.ringSheaf (ringedSite Rc).O)` while the
    -- unit is one of `SheafOfModules (structureSheaf Rc)`, so a binary biproduct of the two is a
    -- goal that is not type-correct at the transparency instance search uses; search for it fails
    -- whichever of the two spellings the ambient category is pinned at. Both instances the
    -- comparison needs are therefore supplied by term, from the classes that quantify over all
    -- pairs of objects.
    have : HasBinaryBiproduct (C := SheafOfModules.{u} (structureSheaf Rc))
        (RingedSite.unitPower (ringedSite Rc) r)
        (_root_.SheafOfModules.unit (structureSheaf Rc)) :=
      HasBinaryBiproducts.has_binary_biproduct _ _
    have : PreservesBinaryBiproduct (C := SheafOfModules.{u} (structureSheaf Rc))
        (RingedSite.unitPower (ringedSite Rc) r)
        (_root_.SheafOfModules.unit (structureSheaf Rc))
        (AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheaf Rc) x) :=
      PreservesBinaryBiproducts.preserves
    exact Projective.of_iso
      (Functor.mapBiprod (AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheaf Rc) x)
        (RingedSite.unitPower (ringedSite Rc) r)
        (_root_.SheafOfModules.unit (structureSheaf Rc))).symm inferInstance

omit [∀ T : Opens X, HasSheafify ((Opens.grothendieckTopology X).over T) AddCommGrpCat.{u}]
    [∀ T : Opens X, ((Opens.grothendieckTopology X).over T).WEqualsLocallyBijective
      AddCommGrpCat.{u}] in
/-- **The stalk of a direct summand of a finite free module is a projective module.** A functor
carries a retraction to a retraction, so the stalk of `M` is a retract of the stalk of
`O_X^{⊕r}`, which is projective by `projective_stalk_unitPower`. -/
lemma projective_stalk_of_isFiniteFreeSummand {M : StructureSheafModules Rc}
    (hM : RingedSite.IsFiniteFreeSummand (ringedSite Rc) M) :
    Projective ((AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheaf Rc) x).obj M) := by
  obtain ⟨r, ⟨ρ⟩⟩ := hM
  have := projective_stalk_unitPower Rc x r
  exact (ρ.map (AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheaf Rc) x)).projective

/-! #### Germ-local form

The statements above need the retraction onto a finite free module on all of `X`. What the stalk
at `x` actually depends on is a retraction over a neighbourhood of `x`, and that is what the two
declarations below use.
-/

section GermLocal

variable {M N : StructureSheafModules Rc} {V : Opens X}

/-- **The stalk at `x` of a homomorphism defined only over a neighbourhood of `x`.** A morphism
`M|_V ⟶ N|_V` of the restrictions to an open `V ∋ x` induces a map of stalks at `x`, because the
stalk is a colimit over the neighbourhoods of `x` and those contained in `V` suffice. This is
`Stacks.SheafOfModules.SheafHomStalk.stalkLinearMap` read over the `RingCat`-valued stalk ring,
by conjugating with `stalkRelabelIso`; no new linearity is proved. -/
def stalkMapOfOver (φ : M.over V ⟶ N.over V) (hxV : x ∈ V) :
    (AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheaf Rc) x).obj M ⟶
      (AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheaf Rc) x).obj N :=
  (stalkRelabelIso Rc x M).inv ≫
    (relabelStalk Rc x).map (ModuleCat.ofHom (stalkLinearMap φ hxV)) ≫
      (stalkRelabelIso Rc x N).hom

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ T : Opens X, HasSheafify ((Opens.grothendieckTopology X).over T) AddCommGrpCat.{u}]
    [∀ T : Opens X, ((Opens.grothendieckTopology X).over T).WEqualsLocallyBijective
      AddCommGrpCat.{u}] in
/-- Taking the stalk at `x` of a homomorphism over `V` is compatible with composition. -/
lemma stalkMapOfOver_comp {P : StructureSheafModules Rc} (φ : M.over V ⟶ N.over V)
    (ψ : N.over V ⟶ P.over V) (hxV : x ∈ V) :
    stalkMapOfOver Rc x (φ ≫ ψ) hxV =
      stalkMapOfOver Rc x φ hxV ≫ stalkMapOfOver Rc x ψ hxV := by
  have h : ModuleCat.ofHom (stalkLinearMap (φ ≫ ψ) hxV) =
      ModuleCat.ofHom (stalkLinearMap φ hxV) ≫ ModuleCat.ofHom (stalkLinearMap ψ hxV) :=
    congrArg ModuleCat.ofHom (stalkLinearMap_comp φ ψ hxV)
  simp only [stalkMapOfOver, h, Functor.map_comp, Category.assoc,
    Iso.hom_inv_id_assoc]

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ T : Opens X, HasSheafify ((Opens.grothendieckTopology X).over T) AddCommGrpCat.{u}]
    [∀ T : Opens X, ((Opens.grothendieckTopology X).over T).WEqualsLocallyBijective
      AddCommGrpCat.{u}] in
/-- Taking the stalk at `x` of the identity over `V` is the identity. -/
lemma stalkMapOfOver_id (hxV : x ∈ V) :
    stalkMapOfOver Rc x (𝟙 (M.over V)) hxV = 𝟙 _ := by
  have h : ModuleCat.ofHom (stalkLinearMap (𝟙 (M.over V)) hxV) =
      𝟙 (ModuleCat.of (ringStalk Rc x) (modStalk M x)) := by
    rw [show (𝟙 (M.over V)) = SheafOfModules.Hom.over (𝟙 M) V from
        ((SheafOfModules.overFunctor (structureSheaf Rc) V).map_id M).symm,
      stalkLinearMap_over, modStalkMap_id]
    rfl
  have h2 : (relabelStalk Rc x).map
      (𝟙 (ModuleCat.of (ringStalk Rc x) (modStalk M x))) = 𝟙 _ :=
    (relabelStalk Rc x).map_id _
  rw [stalkMapOfOver, h, h2, Category.id_comp, Iso.inv_hom_id]

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ T : Opens X, HasSheafify ((Opens.grothendieckTopology X).over T) AddCommGrpCat.{u}]
    [∀ T : Opens X, ((Opens.grothendieckTopology X).over T).WEqualsLocallyBijective
      AddCommGrpCat.{u}] in
/-- **The germ-local form of `projective_stalk_of_isFiniteFreeSummand`.** If `M` is a retract of
`N` over an open neighbourhood `V` of `x` — with no hypothesis on `M` away from `V` — and the
stalk of `N` at `x` is a projective module, then so is the stalk of `M`. The retraction over `V`
is carried to the stalks by `stalkMapOfOver`, which is functorial, so the stalk of `M` is a
retract of the stalk of `N`. -/
lemma projective_stalk_of_retract_over (hxV : x ∈ V) (ρ : Retract (M.over V) (N.over V))
    (hN : Projective ((AlgebraicGeometry.SheafOfModules.stalkFunctor
      (structureSheaf Rc) x).obj N)) :
    Projective ((AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheaf Rc) x).obj M) := by
  have := hN
  exact Retract.projective
    { i := stalkMapOfOver Rc x ρ.i hxV
      r := stalkMapOfOver Rc x ρ.r hxV
      retract := by
        rw [← stalkMapOfOver_comp Rc x ρ.i ρ.r hxV, ρ.retract, stalkMapOfOver_id] }

/-! #### From a finite free summand over `V` -/

section FromSummandOver

/-- **`O_X^{⊕r}` is the free `O_X`-module on `Fin r`.** Both are finite direct sums of `r` copies
of the structure sheaf. -/
def freeIsoUnitPower (r : ℕ) :
    _root_.SheafOfModules.free (R := structureSheaf Rc) (ULift.{u} (Fin r)) ≅
      RingedSite.unitPower (ringedSite Rc) r :=
  RingedSite.InvertibleDerived.freeIsoBiproductFin (structureSheaf Rc) r ≪≫
    (RingedSite.unitPowerIsoBiproduct (ringedSite Rc) r).symm

omit [∀ T : Opens X, HasSheafify ((Opens.grothendieckTopology X).over T) AddCommGrpCat.{u}]
    [∀ T : Opens X, ((Opens.grothendieckTopology X).over T).WEqualsLocallyBijective
      AddCommGrpCat.{u}] in
/-- The stalk of a finite free `O_X`-module is a projective module. -/
lemma projective_stalk_free (r : ℕ) :
    Projective ((AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheaf Rc) x).obj
      (_root_.SheafOfModules.free (R := structureSheaf Rc) (ULift.{u} (Fin r)))) := by
  have := projective_stalk_unitPower Rc x r
  exact Projective.of_iso
    ((AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheaf Rc) x).mapIso
      (freeIsoUnitPower Rc r)).symm inferInstance

/-- The free `O_V`-module on `Fin r` is the restriction to `V` of the free `O_X`-module on
`Fin r`: restriction to the slice preserves the coproduct defining a free module and carries the
structure sheaf to the structure sheaf. -/
def freeOverIso (V : Opens X) (r : ℕ) :
    _root_.SheafOfModules.free (R := (structureSheaf Rc).over V) (ULift.{u} (Fin r)) ≅
      (_root_.SheafOfModules.free (R := structureSheaf Rc) (ULift.{u} (Fin r))).over V :=
  Stacks.Sheaves.GlobalTypeComparison.mapFreeIso
    (Φ := SheafOfModules.overFunctor.{u} (structureSheaf Rc) V)
    (u := FiniteTypeKernel.unitOverIso (R := structureSheaf Rc) V) (ULift.{u} (Fin r))

/-- **The germ-local form of `projective_stalk_of_isFiniteFreeSummand`.** If `M` is a direct
summand of a finite free module *on an open neighbourhood `V` of `x`* — with no hypothesis on `M`
away from `V` — then its stalk at `x` is a projective module.

The retraction over `V` is onto a finite free `O_V`-module, which is the restriction of a finite
free `O_X`-module, so `projective_stalk_of_retract_over` applies with `projective_stalk_free`. -/
lemma projective_stalk_of_isDirectSummandOfFiniteFree_over {M : StructureSheafModules Rc}
    {V : Opens X} (hxV : x ∈ V)
    (hM : ∃ r : ℕ, Nonempty (Retract (M.over V)
      (_root_.SheafOfModules.free (R := (structureSheaf Rc).over V) (ULift.{u} (Fin r))))) :
    Projective ((AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheaf Rc) x).obj M) := by
  obtain ⟨r, ⟨ρ⟩⟩ := hM
  exact projective_stalk_of_retract_over Rc x hxV (ρ.trans (freeOverIso Rc V r).retract)
    (projective_stalk_free Rc x r)

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **A direct summand of a finite free module on a neighbourhood of `x` has a local presentation
at `x`.** `Stacks.SheafOfModules.exists_isFinite_presentation_of_retract` turns the retraction
over `V` into a finite presentation of `M|_V`, and
`Stacks.SheafOfModules.localPresentationOfPresentation` turns that into section-level presentation
data for `M` on a neighbourhood of `x`. -/
lemma nonempty_localPresentation_of_isDirectSummandOfFiniteFree_over
    {M : StructureSheafModules Rc} {V : Opens X} (hxV : x ∈ V)
    (hM : ∃ r : ℕ, Nonempty (Retract (M.over V)
      (_root_.SheafOfModules.free (R := (structureSheaf Rc).over V) (ULift.{u} (Fin r))))) :
    Nonempty (Stacks.SheafOfModules.LocalPresentation M x) := by
  obtain ⟨r, ⟨ρ⟩⟩ := hM
  obtain ⟨P, hP⟩ :=
    Stacks.SheafOfModules.exists_isFinite_presentation_of_retract ρ.i ρ.r ρ.retract
  have := hP
  exact ⟨Stacks.SheafOfModules.localPresentationOfPresentation M P hxV⟩

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **Stacks 01CP for a source which is a finite free summand only near `x`.** The canonical map
of Stacks 01CP out of the stalk of `Hom_{O_X}(M, N)` is bijective as soon as `M` is a direct
summand of a finite free module on an open neighbourhood of `x`; the target `N` is arbitrary and
nothing is assumed about `M` away from that neighbourhood. -/
lemma bijective_sheafHomStalkLinearMap_of_isDirectSummandOfFiniteFree_over
    {M : StructureSheafModules Rc} (N : StructureSheafModules Rc)
    {V : Opens X} (hxV : x ∈ V)
    (hM : ∃ r : ℕ, Nonempty (Retract (M.over V)
      (_root_.SheafOfModules.free (R := (structureSheaf Rc).over V) (ULift.{u} (Fin r))))) :
    Function.Bijective (sheafHomStalkLinearMap (internalHomSheafHom Rc M N) x) :=
  (nonempty_localPresentation_of_isDirectSummandOfFiniteFree_over Rc x hxV hM).elim fun LP =>
    SheafHomStalk.bijective_sheafHomStalkLinearMap_of_localPresentation
      (internalHomSheafHom Rc M N) x LP

end FromSummandOver

end GermLocal

end Projectivity

/-! ### The isomorphism -/

section Assembly

attribute [local instance] HasDerivedCategory.standard

/-- A degree above which `E` vanishes, chosen from the finiteness of the set of degrees in which
it does not. -/
def stalkBound : ℤ := hE.bddAbove.choose

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ T : Opens X, HasSheafify ((Opens.grothendieckTopology X).over T) AddCommGrpCat.{u}]
    [∀ T : Opens X, ((Opens.grothendieckTopology X).over T).WEqualsLocallyBijective
      AddCommGrpCat.{u}] in
include hE in
/-- Boundedness of `E` bounds the complex of stalks above: the stalk functor is additive, so it
carries a zero term to a zero term. -/
lemma isStrictlyLE_stalkComplex :
    CochainComplex.IsStrictlyLE (stalkComplex Rc x E) (stalkBound Rc E hE) := by
  refine (CochainComplex.isStrictlyLE_iff _ _).2 fun i hi => ?_
  refine Functor.map_isZero
    (AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheaf Rc) x) ?_
  by_contra hz
  exact absurd (hE.bddAbove.choose_spec (show i ∈ {j : ℤ | ¬ IsZero (E.X j)} from hz))
    (by simp only [stalkBound] at hi; omega)

include hE in
/-- **Stacks 0GM8, case (1), for a source which is strictly perfect only near `x`.** Let `E` be a
bounded complex of `O_X`-modules each of whose terms is, *on one open neighbourhood `V` of `x`*, a
direct summand of a finite free module — with no hypothesis whatsoever on `E` away from `V` — and
let `F` be arbitrary. Then the derived internal Hom commutes with taking the stalk at `x`:

`RSheafHom_{O_X}(E, F)_x ≅ RHom_{O_{X,x}}(E_x, F_x)`.

Tag 08DM is not used, and could not be: with the hypothesis supported only near `x` the canonical
comparison `Q(SheafHom(E, F)) ⟶ RSheafHom(E, F)` need not be invertible. Its place is taken by
the K-injective model `derivedSheafHomComparison`, which represents `RSheafHom(E, I)` by
`SheafHom(E, I)` for a K-injective `I` **with no hypothesis on `E` at all**; `F` is replaced by
its K-injective resolution, which changes neither side of the statement because the augmentation
is a quasi-isomorphism. Everything after that is germ-local: the stalk of `SheafHom(E, I)` is
computed by `stalkHomComplexIsoOverStalkRing` from Stacks 01CP at the terms of `E`, which
`bijective_sheafHomStalkLinearMap_of_isDirectSummandOfFiniteFree_over` supplies from the
retraction over `V` alone, and the terms of the complex of stalks of `E` are projective by
`projective_stalk_of_isDirectSummandOfFiniteFree_over`, again from that retraction alone. -/
def derivedStalkDerivedSheafHomIsoNearPoint (V : Opens X) (hxV : x ∈ V)
    (hterm : ∀ i : ℤ, ∃ r : ℕ, Nonempty (Retract ((E.X i).over V)
      (_root_.SheafOfModules.free (R := (structureSheaf Rc).over V) (ULift.{u} (Fin r))))) :
    (AlgebraicGeometry.SheafOfModules.derivedStalkFunctor (structureSheaf Rc) x).obj
        (((derivedSheafHom Rc).obj (op (DerivedCategory.Q.obj E))).obj
          (DerivedCategory.Q.obj F)) ≅
      (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, 0, u + 1} (stalkRing Rc x)).hom.obj
        (op ((AlgebraicGeometry.SheafOfModules.derivedStalkFunctor (structureSheaf Rc) x).obj
            (DerivedCategory.Q.obj E)),
          (AlgebraicGeometry.SheafOfModules.derivedStalkFunctor (structureSheaf Rc) x).obj
            (DerivedCategory.Q.obj F)) := by
  haveI := isStrictlyLE_stalkComplex Rc E hE x
  haveI : ∀ i, Projective ((stalkComplex Rc x E).X i) := fun i =>
    projective_stalk_of_isDirectSummandOfFiniteFree_over Rc x hxV (hterm i)
  -- Replace `F` by a K-injective resolution; the augmentation is a quasi-isomorphism.
  -- The resolution and its augmentation are read at the spelling `F` lives at,
  -- `StructureSheafModules Rc`, rather than the `Tensor.ringSheaf (ringedSite Rc).O` one that
  -- `RingedSite.kInjectiveResolution` states them over. Their two properties are then named at
  -- that spelling: searched for, they are goals mentioning `F` across the two presentations of
  -- the ring sheaf, which instance search does not cross.
  let I : CochainComplex (StructureSheafModules Rc) ℤ :=
    (RingedSite.kInjectiveResolution (ringedSite Rc)).obj F
  haveI : I.IsKInjective :=
    Stacks.Injectives.kInjectiveResolutionFunctor_obj_isKInjective _ F
  let ι : F ⟶ I := (RingedSite.kInjectiveAugmentation (ringedSite Rc)).app F
  haveI : IsIso (DerivedCategory.Q.map ι) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ ι).2
      (Stacks.Injectives.kInjectiveResolutionInclusion_quasiIso _ F)
  have h01 : ∀ i j : ℤ, Function.Bijective
      (sheafHomStalkLinearMap (internalHomSheafHom Rc (E.X i) (I.X j)) x) := fun i j =>
    bijective_sheafHomStalkLinearMap_of_isDirectSummandOfFiniteFree_over Rc x _ hxV (hterm i)
  exact (AlgebraicGeometry.SheafOfModules.derivedStalkFunctor (structureSheaf Rc) x).mapIso
      (((derivedSheafHom Rc).obj (op (DerivedCategory.Q.obj E))).mapIso
          (asIso (DerivedCategory.Q.map ι)) ≪≫
        derivedSheafHomComparison Rc E I) ≪≫
    (AlgebraicGeometry.SheafOfModules.derivedStalkFunctorFactors (structureSheaf Rc) x).app
      (RingedSite.sheafHomComplex (ringedSite Rc) E I).obj ≪≫
    DerivedCategory.Q.mapIso (stalkHomComplexIsoOverStalkRing Rc E I hE x h01) ≪≫
    (StacksDraft.DerivedHom.projectiveHomModelIsoOverRing.{u} (stalkRing Rc x)
      (stalkComplex Rc x E) (stalkComplex Rc x I) (stalkBound Rc E hE)).symm ≪≫
    (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, 0, u + 1}
        (stalkRing Rc x)).hom.mapIso
      (Iso.prod
        ((AlgebraicGeometry.SheafOfModules.derivedStalkFunctorFactors
          (structureSheaf Rc) x).app E).op
        (((AlgebraicGeometry.SheafOfModules.derivedStalkFunctorFactors
            (structureSheaf Rc) x).app I).symm ≪≫
          ((AlgebraicGeometry.SheafOfModules.derivedStalkFunctor (structureSheaf Rc) x).mapIso
            (asIso (DerivedCategory.Q.map ι))).symm))

include hE hterm in
/-- **Stacks 0GM8, case (1), for a strictly perfect source.** For `E` a strictly perfect complex
of `O_X`-modules — bounded, with every term a direct summand of a finite free module — and `F`
an arbitrary complex, the derived internal Hom commutes with taking the stalk at `x`:

`RSheafHom_{O_X}(E, F)_x ≅ RHom_{O_{X,x}}(E_x, F_x)`,

the right-hand side being `RHom` in the bundle of Stacks 0A63 over the stalk ring.

The chain is: Stacks 08DM replaces `RSheafHom(E, F)` by the ordinary internal Hom complex
`SheafHom(E, F)`; exactness of the stalk functor turns its derived stalk into the class of its
complex of stalks; `stalkHomComplexIsoOverStalkRing` computes that complex of stalks as the Hom
complex of the complexes of stalks; and Stacks 0A66, in the form
`StacksDraft.DerivedHom.projectiveHomModelIsoOverRing`, recognises that Hom complex as `RHom`,
the complex of stalks of `E` being bounded above with projective terms. -/
def derivedStalkDerivedSheafHomIso :
    (AlgebraicGeometry.SheafOfModules.derivedStalkFunctor (structureSheaf Rc) x).obj
        (((derivedSheafHom Rc).obj (op (DerivedCategory.Q.obj E))).obj
          (DerivedCategory.Q.obj F)) ≅
      (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, 0, u + 1} (stalkRing Rc x)).hom.obj
        (op ((AlgebraicGeometry.SheafOfModules.derivedStalkFunctor (structureSheaf Rc) x).obj
            (DerivedCategory.Q.obj E)),
          (AlgebraicGeometry.SheafOfModules.derivedStalkFunctor (structureSheaf Rc) x).obj
            (DerivedCategory.Q.obj F)) := by
  haveI := isStrictlyLE_stalkComplex Rc E hE x
  haveI : ∀ i, Projective ((stalkComplex Rc x E).X i) := fun i =>
    projective_stalk_of_isFiniteFreeSummand Rc x (hterm i)
  haveI := strictlyPerfectHomComparison_isIso Rc E F hE hterm
  have h01 : ∀ i j : ℤ, Function.Bijective
      (sheafHomStalkLinearMap (internalHomSheafHom Rc (E.X i) (F.X j)) x) := fun i j => by
    letI : (E.X i).IsFinitePresentation := (hterm i).isFinitePresentation (ringedSite Rc)
    exact ⟨SheafHomStalk.injective_sheafHomStalkLinearMap _ x,
      SheafHomStalk.surjective_sheafHomStalkLinearMap _ x⟩
  exact (AlgebraicGeometry.SheafOfModules.derivedStalkFunctor (structureSheaf Rc) x).mapIso
      (asIso (strictlyPerfectHomComparison Rc E F)).symm ≪≫
    (AlgebraicGeometry.SheafOfModules.derivedStalkFunctorFactors (structureSheaf Rc) x).app
      (RingedSite.sheafHomComplex (ringedSite Rc) E F).obj ≪≫
    DerivedCategory.Q.mapIso (stalkHomComplexIsoOverStalkRing Rc E F hE x h01) ≪≫
    (StacksDraft.DerivedHom.projectiveHomModelIsoOverRing.{u} (stalkRing Rc x)
      (stalkComplex Rc x E) (stalkComplex Rc x F) (stalkBound Rc E hE)).symm ≪≫
    (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, 0, u + 1} (stalkRing Rc x)).hom.mapIso
      (Iso.prod
        ((AlgebraicGeometry.SheafOfModules.derivedStalkFunctorFactors
          (structureSheaf Rc) x).app E).op
        ((AlgebraicGeometry.SheafOfModules.derivedStalkFunctorFactors
          (structureSheaf Rc) x).app F).symm)

end Assembly

end Stacks.SheafOfModules.DerivedHomStalk

end
