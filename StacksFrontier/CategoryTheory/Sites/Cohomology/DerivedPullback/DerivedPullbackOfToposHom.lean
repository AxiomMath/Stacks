module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullback
public import StacksFrontier.CategoryTheory.Localization.LeftDerivedByResolutions
public import StacksFrontier.Algebra.Homology.DerivedCategory.HigherDerivedFunctors
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.Homology.PseudoCoherent.BaseChange
public import StacksCore.Tactic.StacksAttribute

/-!
# The derived pullback of a morphism of ringed topoi, at independent universes

Let `f : (Sh(C), 𝒪) ⟶ (Sh(D), 𝒪')` be a morphism of ringed topoi.  Tag 06YY asserts that there
is an exact functor of triangulated categories `Lf^* : D(𝒪') ⥤ D(𝒪)`, the total left derived
functor of degreewise pullback, computing `f^*𝒦^•` on a K-flat complex `𝒦^•` with flat terms.

This file constructs that functor **with the six universes of the two ringed topoi free**: the
objects, the morphisms and the sections of the structure sheaf of each side are unconstrained,
and the two sides are unrelated.  The geometric datum is an
`AlgebraicGeometry.RingedToposHom`, the two-field morphism of ringed topoi of Stacks 01D3,
part (2) — a morphism of the underlying *topoi* together with the structure map — so no functor
between the underlying sites is asked for.

Both generalizations are needed by the small étale ringed topos of an algebraic space.  That
ringed topos is `AlgebraicGeometry.RingedTopos.{u, u + 1, u}`: its objects (the étale scheme
charts) live in `Type (u + 1)`, while its morphisms and the sections of its structure sheaf live
in `Type u`.  And a morphism of algebraic spaces induces no functor between the small étale
sites — the base change of an étale *scheme* chart along a non-representable morphism is an
algebraic space and not a chart — so its morphism of ringed topoi,
`AlgebraicGeometry.Space.smallEtaleRingedToposHom`, is an `AlgebraicGeometry.RingedToposHom` and
not an `AlgebraicGeometry.RingedToposSiteHom`.

## Main definitions

* `Stacks.Cohomology.DerivedPullbackOfToposHom.pullbackOnHomotopy`: degreewise pullback of
  sheaves of modules followed by localization to the derived category.
* `Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback`: **Tag 06YY**, the derived
  pullback `Lf^*`, with its canonical comparison
  `Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackComparison`.

## Main results

* `Stacks.Cohomology.DerivedPullbackOfToposHom.pullbackOnHomotopy_hasLeftDerivedFunctor`:
  a resolving datum for `f^*` — a class of complexes which resolves every complex and on whose
  quasi-isomorphisms `f^*` is inverted — gives `Lf^*` on the whole of `D(𝒪')`.
* `Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback_commShift`: `Lf^*` commutes
  with the shift.
* `Stacks.Cohomology.DerivedPullbackOfToposHom.isIso_derivedPullbackComparison_app`: the
  computation assertion, at any object of a resolving class — in particular at a K-flat complex
  with flat terms, once that class is known to resolve.
* `Stacks.Cohomology.DerivedPullbackOfToposHom.pullbackInvertsQuasiIso_top` and
  `pullbackOnHomotopy_hasLeftDerivedFunctor_of_exact`: the datum is satisfiable, and `Lf^*`
  exists outright along a morphism whose degreewise pullback is exact.

## Implementation notes

*Where the universe collapse of the existing construction comes from, and why it is not needed.*
`Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPullback`
(`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPushforward/AdjunctionForRingedTopoi.lean`)
is stated at `AlgebraicGeometry.RingedTopos.{w, w, w}` for an
`AlgebraicGeometry.RingedToposSiteHom`.  Three separate things pin it there, and only the first
is about the derived pullback itself.

1. Its degreewise pullback is `AlgebraicGeometry.RingedToposSiteHom.pullbackTopos`, which
   `StacksFrontier/CategoryTheory/Sites/Modules/RingedToposHom.lean` declares inside a section whose
   `variable` line reads `{X Y : RingedTopos.{w, w, w}}`.  The reason is that it is Mathlib's
   `SheafOfModules.pullback`, whose existence hypothesis
   `(SheafOfModules.pushforward φ).IsRightAdjoint` Mathlib discharges only for two sites that are
   `CategoryTheory.SmallCategory` in the universe of the rings.  That is pure convenience twice
   over: the generalization of the hypothesis to an essentially small source site is already in
   the tree (`SheafOfModules.pushforward_isRightAdjoint_of_essentiallySmall`), and the pullback
   used below is `Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules` — the
   inverse image of Stacks 03D2 followed by extension of scalars along `f⁻¹𝒪' ⟶ 𝒪`, which is the
   formula of Stacks 03D6, part (2) — which is stated at six free universes and needs no such
   hypothesis.
2. `f.u.IsMorphismOfSites`, carried by the ringed-*site* statements of that chain, is
   `CategoryTheory.Functor.IsMorphismOfSites`, available only for two sites that are
   `CategoryTheory.SmallCategory` in one and the same universe.  Nothing below mentions it: the
   left exactness of the inverse image is a field of `AlgebraicGeometry.MorphismOfTopoi` and
   hence of `AlgebraicGeometry.RingedToposHom`, so a morphism of ringed topoi in the source's
   sense carries it by construction rather than as an extra hypothesis.
3. The *discharge* of the resolving datum by Tag 06YS,
   `Stacks.SheafOfModules.KFlatResolution.exists_kFlatResolution`, asks for
   `CategoryTheory.SmallCategory` of the site, and that one is **not** generalized here; see the
   next note.  It is carried as the hypothesis `hP`, exactly as the `{w, w, w}` development
   carries its own resolving datum, and the 06YY clauses tagged below do not consume it.

*What the resolving datum still costs at an essentially small site.*  Tag 06YS resolves a complex
of `𝒪'`-modules by a direct sum of extensions by zero `j_{U!}𝒪_U` indexed by the *sections* of
the complex over the objects of the site.  On a site whose objects live in `Type (u + 1)` that
index type is not `u`-small, so the direct sum does not exist in `SheafOfModules.{u}` and the
construction does not transpose; only the equivalent small model of the site admits it.  That is
a property of this particular resolution and not of `Lf^*`, which is why the datum is a
parameter here and the tagged clauses are stated without it.

*Proof irrelevance of the instance argument.*  `Functor.HasLeftDerivedFunctor` is a `Prop`-valued
class, so `derivedPullback f` is the same functor whichever witness is supplied, and a consumer
which has one supplies it with `have`.

*The derived category model.*  `CategoryTheory.HasDerivedCategory.standard` is installed as a
file-local instance at high priority, as in the `{w, w, w}` development: the locally small model
`SheafOfModules.hasDerivedCategory` is a global instance but is available only for a site which
is small on the nose, so it does not apply at the universes this file exists for.

## References

* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u w v' u' w'

namespace Stacks.Cohomology.DerivedPullbackOfToposHom

open AlgebraicGeometry AlgebraicGeometry.RingedToposHom

attribute [local instance 10000] HasDerivedCategory.standard

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  (f : RingedToposHom X Y)

/-- Degreewise pullback of sheaves of modules along a morphism of ringed topoi, followed by
localization to the derived category.  A left derived functor of this functor is a derived
pullback `Lf^*`. -/
noncomputable abbrev pullbackOnHomotopy :
    HomotopyCategory (SheafOfModules.{w'} (SheafOfModules.Tensor.ringSheaf Y.O))
        (ComplexShape.up ℤ) ⥤
      DerivedCategory (SheafOfModules.{w} (SheafOfModules.Tensor.ringSheaf X.O)) :=
  (f.toModulesHom.pullbackModules).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh

/-- The quasi-isomorphisms of complexes of `𝒪'`-modules, the class `Lf^*` is the total left
derived functor along. -/
abbrev quasiIsoTarget :
    MorphismProperty
      (HomotopyCategory (SheafOfModules.{w'} (SheafOfModules.Tensor.ringSheaf Y.O))
        (ComplexShape.up ℤ)) :=
  HomotopyCategory.quasiIso (SheafOfModules.{w'} (SheafOfModules.Tensor.ringSheaf Y.O))
    (ComplexShape.up ℤ)

section Datum

/-- The resolving property: every complex of `𝒪'`-modules receives a quasi-isomorphism from one
satisfying `P`. -/
abbrev HasResolutions
    (P : ObjectProperty
      (HomotopyCategory (SheafOfModules.{w'} (SheafOfModules.Tensor.ringSheaf Y.O))
        (ComplexShape.up ℤ))) : Prop :=
  ∀ M : HomotopyCategory (SheafOfModules.{w'} (SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ),
    ∃ (K : HomotopyCategory (SheafOfModules.{w'} (SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ)) (_ : P K) (s : K ⟶ M), quasiIsoTarget (Y := Y) s

variable (P : ObjectProperty
  (HomotopyCategory (SheafOfModules.{w'} (SheafOfModules.Tensor.ringSheaf Y.O))
    (ComplexShape.up ℤ)))

/-- The exactness property: degreewise pullback carries a quasi-isomorphism between complexes
satisfying `P` to an isomorphism of derived categories. -/
abbrev PullbackInvertsQuasiIso : Prop :=
  ∀ {K M : HomotopyCategory (SheafOfModules.{w'} (SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ)}
    (s : K ⟶ M), quasiIsoTarget (Y := Y) s → P K → P M →
      IsIso ((pullbackOnHomotopy f).map s)

variable (hP : HasResolutions (Y := Y) P) (hinv : PullbackInvertsQuasiIso f P)

include hP hinv in
/-- Resolutions by `P` compute the derived pullback pointwise. -/
theorem pullbackOnHomotopy_hasPointwiseLeftDerivedFunctor :
    (pullbackOnHomotopy f).HasPointwiseLeftDerivedFunctor (quasiIsoTarget (Y := Y)) :=
  LeftDerivedByResolutions.hasPointwiseLeftDerivedFunctor_of_resolutions
    (quasiIsoTarget (Y := Y)) P hP (pullbackOnHomotopy f) hinv

include hP hinv in
/-- **A resolving datum gives the unbounded derived pullback.**  Degreewise pullback followed by
localization has an everywhere-defined left derived functor, so `Lf^*` is defined on the whole
of `D(𝒪')`. -/
theorem pullbackOnHomotopy_hasLeftDerivedFunctor :
    (pullbackOnHomotopy f).HasLeftDerivedFunctor (quasiIsoTarget (Y := Y)) :=
  have := pullbackOnHomotopy_hasPointwiseLeftDerivedFunctor f P hP hinv
  Functor.hasLeftDerivedFunctor_of_hasPointwiseLeftDerivedFunctor _ _

end Datum

section Main

variable [(pullbackOnHomotopy f).HasLeftDerivedFunctor (quasiIsoTarget (Y := Y))]

/-- **Tag 06YY, the derived pullback functor, at independent universes.**  The derived pullback
`Lf^* : D(𝒪') ⥤ D(𝒪)` along a morphism of ringed topoi, the total left derived functor of
degreewise pullback followed by localization.

The two ringed topoi have all six of their universes free, and the geometric datum is the
two-field morphism of ringed topoi of Stacks 01D3, part (2); in particular this applies to the
small étale ringed topos `AlgebraicGeometry.RingedTopos.{u, u + 1, u}` of an algebraic space,
which `Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPullback` does not.

The instance argument is `Prop`-valued and is supplied by
`pullbackOnHomotopy_hasLeftDerivedFunctor` from a resolving datum for `f^*`. -/
@[stacks 06YY "the derived pullback functor, for a morphism of ringed topoi whose two ringed
topoi have their object, morphism and structure-ring universes free and unrelated, and whose
geometric datum is a morphism of the underlying topoi rather than of the underlying sites"]
noncomputable abbrev derivedPullback :
    DerivedCategory (SheafOfModules.{w'} (SheafOfModules.Tensor.ringSheaf Y.O)) ⥤
      DerivedCategory (SheafOfModules.{w} (SheafOfModules.Tensor.ringSheaf X.O)) :=
  (pullbackOnHomotopy f).totalLeftDerived DerivedCategory.Qh (quasiIsoTarget (Y := Y))

/-- **Tag 06YY, the canonical comparison, at independent universes.**  The comparison
`Lf^* ⟶ f^*` from the derived pullback to degreewise pullback, whose invertibility on a
resolving class is the computation assertion of Tag 06YY. -/
@[stacks 06YY "the canonical comparison `Lf^* ⟶ f^*`, at free and unrelated universes for the
two ringed topoi and for a geometric datum which is a morphism of the underlying topoi"]
noncomputable abbrev derivedPullbackComparison :
    DerivedCategory.Qh ⋙ derivedPullback f ⟶ pullbackOnHomotopy f :=
  (pullbackOnHomotopy f).totalLeftDerivedCounit DerivedCategory.Qh (quasiIsoTarget (Y := Y))

/-- **Tag 06YY, compatibility with shifts, at independent universes.**  The derived pullback
commutes with the shift functors of the two derived categories. -/
@[stacks 06YY "compatibility of `Lf^*` with the shift, at free and unrelated universes for the
two ringed topoi"]
noncomputable instance derivedPullback_commShift : (derivedPullback f).CommShift ℤ :=
  StacksDraft.PseudoCoherence.leftDerivedCommShift (derivedPullback f)
    (derivedPullbackComparison f) (quasiIsoTarget (Y := Y)) ℤ

/-- **Tag 06YY, the computation, at independent universes.**  The canonical comparison
`Lf^* 𝒦^• ⟶ f^* 𝒦^•` is invertible at an object of a resolving class for `f^*`: the derived
pullback of such a complex is computed by degreewise pullback.

At the class of K-flat complexes with flat terms, which is the class the source resolves by,
this is the computation assertion of Tag 06YY in the form it states. -/
@[stacks 06YY "the computation `Lf^*𝒦 = f^*𝒦` on a resolving class, at free and unrelated
universes for the two ringed topoi"]
theorem isIso_derivedPullbackComparison_app
    (P : ObjectProperty
      (HomotopyCategory (SheafOfModules.{w'} (SheafOfModules.Tensor.ringSheaf Y.O))
        (ComplexShape.up ℤ)))
    (hP : HasResolutions (Y := Y) P) (hinv : PullbackInvertsQuasiIso f P)
    (K : HomotopyCategory (SheafOfModules.{w'} (SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ))
    (hK : P K) :
    IsIso ((derivedPullbackComparison f).app K) :=
  LeftDerivedByResolutions.isIso_app_of_resolutions (quasiIsoTarget (Y := Y)) P hP
    (pullbackOnHomotopy f) hinv DerivedCategory.Qh (derivedPullback f)
    (derivedPullbackComparison f) K hK

end Main

section Exact

omit [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})] in
/-- The class of all objects resolves every complex, by the identity. -/
theorem hasResolutions_top :
    HasResolutions (Y := Y)
      (⊤ : ObjectProperty
        (HomotopyCategory (SheafOfModules.{w'} (SheafOfModules.Tensor.ringSheaf Y.O))
          (ComplexShape.up ℤ))) :=
  fun M => ⟨M, trivial, 𝟙 M, MorphismProperty.id_mem _ _⟩

variable [PreservesFiniteLimits (f.toModulesHom.pullbackModules)]

/-- An exact degreewise pullback inverts every quasi-isomorphism, so the class of all objects is
a resolving datum for it.  This exhibits the datum as satisfiable. -/
theorem pullbackInvertsQuasiIso_top : PullbackInvertsQuasiIso f ⊤ :=
  have := pullbackModules_preservesFiniteColimits f
  fun _s hs _ _ =>
    Stacks.DerivedFunctor.HigherDerivedOfExact.mapHomotopyCategory_inverts_quasiIso
      (f.toModulesHom.pullbackModules) _ hs

/-- **The derived pullback exists along a morphism of ringed topoi whose degreewise pullback is
exact**, with no resolving datum left over. -/
theorem pullbackOnHomotopy_hasLeftDerivedFunctor_of_exact :
    (pullbackOnHomotopy f).HasLeftDerivedFunctor (quasiIsoTarget (Y := Y)) :=
  pullbackOnHomotopy_hasLeftDerivedFunctor f ⊤ hasResolutions_top (pullbackInvertsQuasiIso_top f)

end Exact

end Stacks.Cohomology.DerivedPullbackOfToposHom

end
