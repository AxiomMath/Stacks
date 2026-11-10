module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GrothendieckAbelian
public import StacksFrontier.Algebra.Homology.DerivedCategory.HigherDerivedFunctors
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.CategoryTheory.Localization.DerivingAdjoints
public import StacksFrontier.CategoryTheory.Localization.LeftDerivedByResolutions
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposPullbackAdjunction
public import StacksFrontier.Homology.HomotopyCategory.QuasiIsoAlongExactFunctor
public import StacksFrontier.Homology.Injectives.Spaltenstein.Enlargement
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.PullbackPushforwardAdjunction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionsOfSize

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

/-!
# The derived pullback is left adjoint to the derived pushforward, for ringed topoi

Let `f : (Sh(C), 𝒪) ⟶ (Sh(D), 𝒪')` be a morphism of ringed topoi.  The unbounded derived
pushforward `Rf_*` is constructed here from K-injective resolutions, and shown to be right
adjoint to the unbounded derived pullback `Lf^*`, with the adjunction compatible with the
canonical comparison maps of the two derived functors.

The pushforward half is unconditional: sheaves of modules over the structure sheaf of a
ringed topos form a Grothendieck abelian category, so every complex admits a
quasi-isomorphism into a K-injective one, and `Rf_*` exists and is computed by K-injective
complexes.

The pullback half is relative to a *resolving datum* for `f^*`: a class `P` of objects of
`K(𝒪')` such that every complex receives a quasi-isomorphism from one in `P`
(`HasResolutions`) and such that `f^*` carries quasi-isomorphisms between complexes in `P`
to isomorphisms of `D(𝒪)` (`PullbackInvertsQuasiIso`).  Such a datum produces `Lf^*` as a
total left derived functor, and makes the adjunction follow.  At the intended class — the
K-flat complexes *with flat terms*, which is the class the source resolves by — the resolving
half is discharged here from Tag 06YS, so that `PullbackInvertsQuasiIso f IsKFlat` —
exactness of `f^*` on that class — is the single remaining input of *this file*.

That input is no longer open. It is discharged for every morphism of ringed topoi coming from a
morphism of sites by
`Stacks.Cohomology.DerivedPullbackOnRingedTopoi.pullbackInvertsQuasiIso_isKFlat` in
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPullback/DerivedPullbackExistence.lean:119`,
and `Lf^*` follows on the next line as
`hasLeftDerivedFunctor_pullbackOnHomotopy` (`:130`).

## Main definitions

* `Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.pushforwardOnHomotopy` is degreewise
  pushforward followed by localization.
* `Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPushforward` is `Rf_*`, with
  comparison
  `Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPushforwardUnit`.
* `Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.pullbackOnHomotopy` is degreewise
  pullback followed by localization.
* `Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPullback` is `Lf^*`, with
  comparison
  `Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPullbackComparison`.
* `Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.homotopyPullbackPushforwardAdjunction` is
  `K(f^*) ⊣ K(f_*)`.
* `derivedPullbackPushforwardAdjunctionOfAbsolute` is the adjunction
  `Lf^* ⊣ Rf_*` under the single hypothesis that remains once the pushforward side is
  discharged.
* `Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPullbackPushforwardAdjunction` is
  that adjunction from a resolving
  datum for `f^*`.
* `Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat` is the class of K-flat complexes
  with flat terms on the unbounded
  homotopy category, and
    `derivedPullbackPushforwardAdjunctionOfKFlat` is the
  adjunction from the one hypothesis that `f^*` inverts the quasi-isomorphisms between
  complexes in that class.
* `derivedPullbackPushforwardAdjunctionOfExact` is that adjunction for a
  morphism along which `f^*` is exact, where no resolving datum is left over.

## Main results

* `Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.exists_quasiIso_isKInjective`: every
  complex of modules on a ringed topos
  admits a quasi-isomorphism into a K-injective complex.
* `Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.pushforward_hasRightDerivedFunctor`:
  `Rf_*` exists on the whole unbounded
  derived category, unconditionally.
* `isIso_derivedPushforwardUnit_app_of_isKInjective`: K-injective complexes
  compute `Rf_*`.
* `Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.hasResolutions_isKFlat`: the K-flat
  complexes with flat terms resolve every
  complex of `𝒪'`-modules, by Tag 06YS.  This is unconditional.
* `Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.comp_isRightDerivedFunctor` and
  `Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.comp_isLeftDerivedFunctor`: absoluteness
    of the two derived functors,
  which is what the derived adjunction consumes.  The first is unconditional.
* `derivedPullbackPushforwardAdjunctionOfAbsolute_unit_fac`,
  `derivedPullbackPushforwardAdjunctionOfAbsolute_counit_fac` and their
  resolving-datum forms
    `derivedPullbackPushforwardAdjunction_unit_fac`,
  `derivedPullbackPushforwardAdjunction_counit_fac`: the compatibility of the
  derived unit and counit with the ordinary ones.

## Implementation notes

*What is unconditional and what is not.*  The source proves this lemma formally from the
existence of `Rf_*` and of `Lf^*`, citing Derived Categories, Lemma 09T5.  The existence of
`Rf_*` is proved here, from the Grothendieck abelianness of `Mod(𝒪)` and the K-injective
resolutions of Tag 079P.  The existence of `Lf^*` is the content of Tag 06YY, which rests on
K-flat resolutions and the exactness of `f^*` on K-flat complexes; it is carried here as a
resolving datum, as in the ringed-space case of Tag 079W.  Unlike there, its resolving half is
discharged: Tag 06YS supplies K-flat resolutions on a ringed site, so `hasResolutions_isKFlat`
holds and the datum collapses to the single hypothesis `PullbackInvertsQuasiIso f IsKFlat`,
which `Stacks.Cohomology.DerivedPullbackOnRingedTopoi.pullbackInvertsQuasiIso_isKFlat`
discharges for every morphism of ringed topoi — downstream of this file, so the datum stays a
parameter in the statements below.

*The resolving class is K-flat **with flat terms**.*  `IsKFlat` carries both clauses, and the
second is not decoration.  Tag 06YS resolves by a complex that is K-flat and termwise flat,
and the source's argument for the exactness of `f^*` on the class — Tag 0G7E, whose inputs
are Tags 05VD, 0G6R and 0G7C — consumes the termwise flatness at every step.  Plain
K-flatness would make `PullbackInvertsQuasiIso f IsKFlat` a strictly stronger hypothesis than
what Tag 06YY proves, so the deferred input would not be discharged by 06YY when it lands;
the narrower class is the faithful one and is still resolving, since 06YS yields the flatness
clause along with the other three.

*Universes of the resolving class.*  `HasResolutions`, `IsKFlat` and `hasResolutions_isKFlat`
speak about the target ringed topos alone, and they are stated with its three universes
independent: writing `RingedTopos.{v₁, u₁, w₁}` for morphisms, objects and sections, nothing
relates `w₁` to `v₁` or `u₁`.  So they apply at a site whose objects lie *above* the universe of
the sections — the small étale site of an algebraic space,
`AlgebraicGeometry.Space.smallEtaleRingedTopos`, which is a `RingedTopos.{u, u + 1, u}`.  Setting
the three to one universe gives back exactly the statements the rest of this file uses, every
instance argument involved being a `Prop`.  Two things make the independence available.  Tag 06YS
is taken in the form whose site universes are free of the module universe,
`Stacks.SheafOfModules.KFlatResolution.exists_kFlatResolution_ofSize`, rather than
`exists_kFlatResolution`, whose resolution is a direct sum of extensions by zero indexed by the
sections over the objects of the site and so does not exist in `SheafOfModules.{w₁}` when the
objects are not `w₁`-small; and the total complex of a double complex of `𝒪'`-modules, which the
K-flatness criteria behind `CochainComplex.KFlatBifunctor.KFlat` take as an instance argument, is
supplied by `Stacks.SheafOfModules.KFlatResolution.hasTotal_ofSize`, which needs only colimits of
shapes in `Type 0` and hence no size condition at all.  The rest of this file stays at
`RingedTopos.{w, w, w}` because `AlgebraicGeometry.RingedToposSiteHom` carries a continuous
functor between the two sites.

*The morphism-of-sites hypothesis.*  `AlgebraicGeometry.RingedToposHom` asks only that the
underlying functor `f.u` be *continuous*; left exactness of `f⁻¹` is not a field of it, and
`AlgebraicGeometry.RingedToposHom.toToposHom` takes `f.u.IsMorphismOfSites Y.J X.J` as a
separate argument precisely for that reason.  A morphism of ringed topoi in the source's
sense has that exactness, and the exactness of `f^*` on the K-flat class is false without it
— it rests on Tags 05VD and 0G6R, which
  `Stacks.Sheaves.DerivedPullback.KFlatPullback.PullbackPreservesIsFlat` and
`Stacks.Sheaves.DerivedPullback.KFlatPullback.PullbackPreservesShortExact` each state with that
  same hypothesis because both
are false for a merely continuous `f.u`.  So the deferred input of the `KFlatDatum` section is
stated as `f.u.IsMorphismOfSites Y.J X.J → PullbackInvertsQuasiIso f IsKFlat`, which is the
spelling Tag 06YY itself uses for it, and the results that
consume it carry `hmos : f.u.IsMorphismOfSites Y.J X.J` too.  **Tag 06YY does not prove it**:
its declarations carry `PullbackInvertsQuasiIso f IsKFlat` as their own parameter `hinv` and
derive their conclusions from it.  The discharge is therefore in a separate module,
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPullback/DerivedPullbackExistence.lean`,
which runs the reduction that does not go in a circle,
`pullbackInvertsQuasiIso_isKFlat_of_acyclic_pullbackComplex`,
which replaces it by acyclicity of the degreewise pullback of an acyclic complex of the class;
its own inputs are Tags 05VD and 0G6R, and both are now concluded in
`StacksFrontier/CategoryTheory/Sites/Modules/FlatMorphisms/PullbackPreservesFlatness.lean`.
The hypothesis is *not* added as
a field of `RingedToposHom`: the two sites of that structure have deliberately independent
universes, which a field stated with `Functor.IsMorphismOfSites` — a notion available only for
small categories in one universe — would collapse.  The generic resolving-datum sections and
`hasResolutions_isKFlat` mention no such hypothesis and need none.

*Mere existence of `Lf^*` is not enough.*  The derived adjunction consumes *absoluteness* of
both derived functors — that `Lf^* ⋙ Rf_*` and `Rf_* ⋙ Lf^*` are again derived functors of
the respective composites — and `HasLeftDerivedFunctor` does not imply it.  For `Rf_*`
absoluteness comes free from Tag 070K, since the comparison of a right derived functor
computed by K-injective resolutions is invertible on the K-injective complexes and stays so
after applying any functor.  For `Lf^*` it is the resolving datum that supplies it, through
`CategoryTheory.LeftDerivedByResolutions.isIso_app_of_resolutions`.

*Reuse of the ringed-space file.*
  `isRightDerivedFunctor_of_isIso_app_isKInjective`
is stated over an arbitrary abelian category, so it is applied here rather than restated;
only the geometric input — the ringed topos in place of the ringed space — differs.

*One spelling for the quasi-isomorphisms.*  `HomotopyCategory.quasiIso` is written out at
each occurrence rather than abbreviated.  The class occurs both as the localizing class of
`DerivedCategory.Qh` and as the argument of `HasLeftDerivedFunctor`, and an abbreviation
folded over one of the two makes the instance arguments of `Functor.totalLeftDerived`, which
precede its explicit class argument, impossible to synthesize.

## References

* [Stacks Project, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
* [Stacks Project, Tag 09T5](https://stacks.math.columbia.edu/tag/09T5)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

universe w

/-- Every complex of modules over the structure sheaf of a ringed topos admits a
quasi-isomorphism into a K-injective complex: the category of such modules is Grothendieck
abelian, so Tag 079P applies. -/
theorem exists_quasiIso_isKInjective (Z : RingedTopos.{w, w, w})
    [Z.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [HasSheafify Z.J AddCommGrpCat.{w}]
    [Z.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (K : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ) :
    ∃ (I : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ)
      (g : K ⟶ I), I.IsKInjective ∧ QuasiIso g := by
  have := SheafOfModules.isGrothendieckAbelianU (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)
  obtain ⟨R⟩ := Stacks.Injectives.exists_functorial_quasiIso_isKInjective.{w}
    (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
  exact ⟨R.functor.obj K, R.inclusion.app K, R.isKInjective K, R.quasiIso K⟩

/-! ### The resolving class, at a target ringed topos with its three universes free -/

section Resolving

universe v₁ u₁ w₁

variable {Y : RingedTopos.{v₁, u₁, w₁}}
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w₁} RingCat.{w₁})]
  [HasSheafify Y.J AddCommGrpCat.{w₁}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w₁}]

attribute [local instance] Stacks.SheafOfModules.KFlatResolution.hasTotal_ofSize

/-- The resolving property: every complex of `𝒪'`-modules receives a quasi-isomorphism from
one satisfying `P`. -/
abbrev HasResolutions
    (P : ObjectProperty (HomotopyCategory (SheafOfModules.{w₁}
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (.up ℤ))) : Prop :=
  ∀ M : HomotopyCategory (SheafOfModules.{w₁} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (.up ℤ),
    ∃ (K : HomotopyCategory (SheafOfModules.{w₁} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        (.up ℤ)) (_ : P K) (s : K ⟶ M),
      HomotopyCategory.quasiIso (SheafOfModules.{w₁}
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (.up ℤ) s

/-- The K-flat complexes of `𝒪'`-modules **with flat terms**, as a property of objects of the
unbounded homotopy category.  This is the intended resolving class for `f^*`, and it is the
class the source resolves by: Tag 06YS produces a resolution that is K-flat *and* termwise
flat, and the termwise flatness is exactly what Tag 0G7E's argument for the exactness of `f^*`
on the class consumes.  Dropping the flatness clause would make
`PullbackInvertsQuasiIso f IsKFlat` strictly stronger than what Tag 06YY proves, hence not
dischargeable by it. -/
def IsKFlat : ObjectProperty (HomotopyCategory (SheafOfModules.{w₁}
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (.up ℤ)) :=
  fun M => @CochainComplex.KFlatBifunctor.KFlat
    (SheafOfModules.{w₁} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (SheafOfModules.{w₁} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (SheafOfModules.{w₁} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    _ _ _ _ _ _
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u₁, v₁, w₁, w₁, w₁} Y.O)
    (Stacks.SheafOfModules.Tensor.sheafTensor_additive.{u₁, v₁, w₁, w₁, w₁} Y.O)
    (Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive.{u₁, v₁, w₁, w₁, w₁} Y.O)
    _ M.as ∧
    ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{v₁, u₁, w₁, w₁} (O := Y.O) (M.as.X i)

omit [Y.J.HasSheafCompose (forget₂ CommRingCat.{w₁} RingCat.{w₁})] in
/-- **The K-flat complexes resolve every complex**, by Tag 06YS: every complex of
`𝒪'`-modules on the site of a ringed topos receives a quasi-isomorphism from a K-flat
complex with flat terms.  This discharges the `HasResolutions` half of a resolving datum at
the K-flat class, leaving `PullbackInvertsQuasiIso f IsKFlat` as the only input. -/
theorem hasResolutions_isKFlat : HasResolutions (IsKFlat (Y := Y)) := by
  intro M
  obtain ⟨N, rfl⟩ := HomotopyCategory.quotient_obj_surjective M
  obtain ⟨K, g, hK, hflat, hg, _⟩ :=
    Stacks.SheafOfModules.KFlatResolution.exists_kFlatResolution_ofSize Y.O N
  refine ⟨(HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K, ⟨hK, hflat⟩,
    (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map g, ?_⟩
  exact (HomotopyCategory.quotient_map_mem_quasiIso_iff g).mpr hg

end Resolving

variable {X Y : RingedTopos.{w, w, w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (f : RingedToposSiteHom X Y)

/-- The adjunction `K(f^*) ⊣ K(f_*)` on the unbounded homotopy categories, induced
degreewise by the adjunction `f^* ⊣ f_*` of Stacks 03D7. -/
noncomputable abbrev homotopyPullbackPushforwardAdjunction :
    f.pullbackTopos.mapHomotopyCategory (.up ℤ) ⊣
      f.pushforwardTopos.mapHomotopyCategory (.up ℤ) :=
  CategoryTheory.Adjunction.mapHomotopyCategoryAdjunction
    f.pullbackPushforwardAdjunctionTopos (.up ℤ)

section Pushforward

variable [HasDerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]

/-- Degreewise pushforward of sheaves of modules along a morphism of ringed topoi, followed
by localization to the derived category.  A right derived functor of this functor is a
derived pushforward `Rf_*`. -/
noncomputable abbrev pushforwardOnHomotopy :
    HomotopyCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (.up ℤ) ⥤
      DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :=
  f.pushforwardTopos.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh

/-- K-injective resolutions compute the derived pushforward pointwise. -/
noncomputable instance pushforward_hasPointwiseRightDerivedFunctor :
    (pushforwardOnHomotopy f).HasPointwiseRightDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (.up ℤ)) :=
  (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{
      w, _, w + 1, w + 1, w + 1, w + 1}
      (pushforwardOnHomotopy f) (exists_quasiIso_isKInjective X)).1

/-- **The unbounded derived pushforward exists**, for every morphism of ringed topoi and
with no further hypothesis: degreewise pushforward followed by localization has a right
derived functor on the whole unbounded derived category `D(𝒪)`. -/
noncomputable instance pushforward_hasRightDerivedFunctor :
    (pushforwardOnHomotopy f).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (.up ℤ)) :=
  Functor.hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor _ _

variable [HasDerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]

/-- The chosen unbounded derived pushforward `Rf_*`, the total right derived functor of
degreewise pushforward followed by localization. -/
noncomputable abbrev derivedPushforward :
    DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
      DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :=
  (pushforwardOnHomotopy f).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (.up ℤ))

/-- The canonical comparison from degreewise pushforward to the derived pushforward. -/
noncomputable abbrev derivedPushforwardUnit :
    pushforwardOnHomotopy f ⟶ DerivedCategory.Qh ⋙ derivedPushforward f :=
  (pushforwardOnHomotopy f).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (.up ℤ))

omit [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- A K-injective complex computes the derived pushforward: on it the canonical comparison
`f_* I ⟶ Rf_* I` is invertible. -/
theorem isIso_derivedPushforwardUnit_app_of_isKInjective
    (I : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hI : I.IsKInjective) :
    IsIso ((derivedPushforwardUnit f).app
      ((HomotopyCategory.quotient (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (.up ℤ)).obj I)) :=
  (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{
      w, _, _, w + 1, w + 1, w + 1}
      (pushforwardOnHomotopy f) (exists_quasiIso_isKInjective X)).2
    DerivedCategory.Qh (derivedPushforward f) (derivedPushforwardUnit f) I hI

end Pushforward

variable [HasDerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]

/-- Degreewise pullback of sheaves of modules along a morphism of ringed topoi, followed by
localization to the derived category. -/
noncomputable abbrev pullbackOnHomotopy :
    HomotopyCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (.up ℤ) ⥤
      DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  f.pullbackTopos.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh

section Pullback

variable (P : ObjectProperty (HomotopyCategory (SheafOfModules.{w}
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (.up ℤ)))

/-- The exactness property: degreewise pullback carries a quasi-isomorphism between
complexes satisfying `P` to an isomorphism of derived categories. -/
abbrev PullbackInvertsQuasiIso : Prop :=
  ∀ {K M : HomotopyCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (.up ℤ)} (s : K ⟶ M),
    HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        (.up ℤ) s → P K → P M →
      IsIso ((pullbackOnHomotopy f).map s)

variable (hP : HasResolutions P) (hinv : PullbackInvertsQuasiIso f P)

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
include hP hinv in
/-- Resolutions by `P` compute the derived pullback pointwise. -/
theorem pullbackOnHomotopy_hasPointwiseLeftDerivedFunctor :
    (pullbackOnHomotopy f).HasPointwiseLeftDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        (.up ℤ)) :=
  LeftDerivedByResolutions.hasPointwiseLeftDerivedFunctor_of_resolutions
    (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (.up ℤ)) P hP
    (pullbackOnHomotopy f) hinv

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
include hP hinv in
/-- Resolutions by `P` give the unbounded derived pullback. -/
theorem pullbackOnHomotopy_hasLeftDerivedFunctor :
    (pullbackOnHomotopy f).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        (.up ℤ)) :=
  have := pullbackOnHomotopy_hasPointwiseLeftDerivedFunctor f P hP hinv
  Functor.hasLeftDerivedFunctor_of_hasPointwiseLeftDerivedFunctor _ _

end Pullback

section

variable [HasDerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
variable [(pullbackOnHomotopy f).HasLeftDerivedFunctor
  (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (.up ℤ))]

/-- **Tag 06YY, the derived pullback functor.**  The derived pullback `Lf^* : D(𝒪') ⥤ D(𝒪)`, the
total left derived functor of degreewise pullback followed by localization.

The instance argument is discharged for every morphism of ringed topoi by
`Stacks.Cohomology.DerivedPullbackOnRingedTopoi.hasLeftDerivedFunctor_pullbackOnHomotopy`, so
this is the functor Tag 06YY asserts to exist. -/
@[stacks 06YY "the derived pullback functor"]
noncomputable abbrev derivedPullback :
    DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⥤
      DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  (pullbackOnHomotopy f).totalLeftDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (.up ℤ))

/-- **Tag 06YY, the canonical comparison.**  The comparison `Lf^* ⟶ f^*` from the derived
pullback to degreewise pullback, whose invertibility on K-flat complexes with flat terms is the
computation assertion of Tag 06YY. -/
@[stacks 06YY "canonical comparison"]
noncomputable abbrev derivedPullbackComparison :
    DerivedCategory.Qh ⋙ derivedPullback f ⟶ pullbackOnHomotopy f :=
  (pullbackOnHomotopy f).totalLeftDerivedCounit DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (.up ℤ))

end

section Absolute

variable [HasDerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
variable [(pullbackOnHomotopy f).HasLeftDerivedFunctor
  (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (.up ℤ))]

omit [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The derived pushforward stays a right derived functor after composing with the derived
pullback: its comparison is invertible on the K-injective complexes, and so is its image
under any functor. -/
theorem comp_isRightDerivedFunctor :
    (derivedPushforward f ⋙ derivedPullback f).IsRightDerivedFunctor
      (Functor.whiskerRight (derivedPushforwardUnit f) (derivedPullback f) ≫
        (Functor.associator DerivedCategory.Qh (derivedPushforward f)
          (derivedPullback f)).hom)
      (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (.up ℤ)) := by
  refine
    isRightDerivedFunctor_of_isIso_app_isKInjective.{
      w, _, _, w + 1, w + 1, w + 1}
    (pushforwardOnHomotopy f ⋙ derivedPullback f) (exists_quasiIso_isKInjective X)
    DerivedCategory.Qh _ _ (fun I hI => ?_)
  have := isIso_derivedPushforwardUnit_app_of_isKInjective f I hI
  rw [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Category.comp_id]
  infer_instance

variable [(derivedPullback f ⋙ derivedPushforward f).IsLeftDerivedFunctor
  ((Functor.associator DerivedCategory.Qh (derivedPullback f) (derivedPushforward f)).inv ≫
    Functor.whiskerRight (derivedPullbackComparison f) (derivedPushforward f))
  (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (.up ℤ))]

/-- **Stacks 07A6 with the pullback side taken as given.**  The adjunction `Lf^* ⊣ Rf_*` on
the unbounded derived categories of sheaves of modules over ringed topoi, under the single
hypothesis that the derived pullback remains a left derived functor after composing with the
derived pushforward.

The pushforward half of the input is discharged here (`comp_isRightDerivedFunctor`), so this
one instance argument is the whole of what the source defers to Tag 06YY.

This and `derivedPullbackPushforwardAdjunction` below state the same adjunction and are not a
duplicated pair: they differ in how the `IsLeftDerivedFunctor` input arrives.  This one takes it
as the instance argument above; the one below takes `(P, hP, hinv)` in its place and discharges
the instance from them by `comp_isLeftDerivedFunctor`, so it calls this one.  Collapsing either
onto the other would force `(P, hP, hinv)` on the callers of this one, or drop that discharge
from the one below. -/
noncomputable def derivedPullbackPushforwardAdjunctionOfAbsolute :
    derivedPullback f ⊣ derivedPushforward f :=
  have := comp_isRightDerivedFunctor f
  (homotopyPullbackPushforwardAdjunction f).derived
    (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (.up ℤ))
    (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (.up ℤ))
    (derivedPullbackComparison f) (derivedPushforwardUnit f)

omit [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The unit of `derivedPullbackPushforwardAdjunctionOfAbsolute` agrees with the ordinary
pullback--pushforward unit after applying the canonical comparison maps. -/
theorem derivedPullbackPushforwardAdjunctionOfAbsolute_unit_fac
    (M : HomotopyCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (.up ℤ)) :
    (derivedPullbackPushforwardAdjunctionOfAbsolute f).unit.app
          (DerivedCategory.Qh.obj M) ≫
        (derivedPushforward f).map ((derivedPullbackComparison f).app M) =
      DerivedCategory.Qh.map ((homotopyPullbackPushforwardAdjunction f).unit.app M) ≫
        (derivedPushforwardUnit f).app
          ((f.pullbackTopos.mapHomotopyCategory (.up ℤ)).obj M) :=
  have := comp_isRightDerivedFunctor f
  (homotopyPullbackPushforwardAdjunction f).derivedη_fac_app
    (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (.up ℤ))
    (derivedPullbackComparison f) (derivedPushforwardUnit f) M

omit [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The counit of `derivedPullbackPushforwardAdjunctionOfAbsolute` agrees with the ordinary
pullback--pushforward counit after applying the canonical comparison maps. -/
theorem derivedPullbackPushforwardAdjunctionOfAbsolute_counit_fac
    (K : HomotopyCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (.up ℤ)) :
    (derivedPullback f).map ((derivedPushforwardUnit f).app K) ≫
        (derivedPullbackPushforwardAdjunctionOfAbsolute f).counit.app
          (DerivedCategory.Qh.obj K) =
      (derivedPullbackComparison f).app
          ((f.pushforwardTopos.mapHomotopyCategory (.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map
          ((homotopyPullbackPushforwardAdjunction f).counit.app K) :=
  have := comp_isRightDerivedFunctor f
  (homotopyPullbackPushforwardAdjunction f).derivedε_fac_app
    (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (.up ℤ))
    (derivedPullbackComparison f) (derivedPushforwardUnit f) K

end Absolute

section Main

variable [HasDerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
variable (P : ObjectProperty (HomotopyCategory (SheafOfModules.{w}
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (.up ℤ)))
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (.up ℤ))]
  (hP : HasResolutions P) (hinv : PullbackInvertsQuasiIso f P)

omit [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
include hP hinv in
/-- The derived pullback stays a left derived functor after composing with the derived
pushforward: its comparison is invertible on the resolving class, and so is its image under
any functor. -/
theorem comp_isLeftDerivedFunctor :
    (derivedPullback f ⋙ derivedPushforward f).IsLeftDerivedFunctor
      ((Functor.associator DerivedCategory.Qh (derivedPullback f)
          (derivedPushforward f)).inv ≫
        Functor.whiskerRight (derivedPullbackComparison f) (derivedPushforward f))
      (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        (.up ℤ)) := by
  refine LeftDerivedByResolutions.isLeftDerivedFunctor_of_isIso_on_resolutions
    (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (.up ℤ)) P hP
    (pullbackOnHomotopy f ⋙ derivedPushforward f)
    (fun s hs hK hM => by
      have := hinv s hs hK hM
      change IsIso ((derivedPushforward f).map ((pullbackOnHomotopy f).map s))
      infer_instance)
    DerivedCategory.Qh _ _ (fun K hK => ?_)
  have := LeftDerivedByResolutions.isIso_app_of_resolutions
    (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (.up ℤ)) P hP
    (pullbackOnHomotopy f) hinv DerivedCategory.Qh (derivedPullback f)
    (derivedPullbackComparison f) K hK
  rw [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_inv_app,
    Category.id_comp]
  infer_instance

include hP hinv in
/-- The adjunction `Lf^* ⊣ Rf_*` on the unbounded derived categories of sheaves of modules
over ringed topoi. -/
noncomputable def derivedPullbackPushforwardAdjunction :
    derivedPullback f ⊣ derivedPushforward f :=
  have := comp_isLeftDerivedFunctor f P hP hinv
  derivedPullbackPushforwardAdjunctionOfAbsolute f

omit [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
include hP hinv in
/-- The derived unit agrees with the ordinary unit after applying the canonical comparison
maps. -/
theorem derivedPullbackPushforwardAdjunction_unit_fac
    (M : HomotopyCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (.up ℤ)) :
    (derivedPullbackPushforwardAdjunction f P hP hinv).unit.app
          (DerivedCategory.Qh.obj M) ≫
        (derivedPushforward f).map ((derivedPullbackComparison f).app M) =
      DerivedCategory.Qh.map ((homotopyPullbackPushforwardAdjunction f).unit.app M) ≫
        (derivedPushforwardUnit f).app
          ((f.pullbackTopos.mapHomotopyCategory (.up ℤ)).obj M) :=
  have := comp_isLeftDerivedFunctor f P hP hinv
  derivedPullbackPushforwardAdjunctionOfAbsolute_unit_fac f M

omit [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
include hP hinv in
/-- The derived counit agrees with the ordinary counit after applying the canonical
comparison maps. -/
theorem derivedPullbackPushforwardAdjunction_counit_fac
    (K : HomotopyCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (.up ℤ)) :
    (derivedPullback f).map ((derivedPushforwardUnit f).app K) ≫
        (derivedPullbackPushforwardAdjunction f P hP hinv).counit.app
          (DerivedCategory.Qh.obj K) =
      (derivedPullbackComparison f).app
          ((f.pushforwardTopos.mapHomotopyCategory (.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map
          ((homotopyPullbackPushforwardAdjunction f).counit.app K) :=
  have := comp_isLeftDerivedFunctor f P hP hinv
  derivedPullbackPushforwardAdjunctionOfAbsolute_counit_fac f K

end Main

section KFlatDatum

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- For a morphism of ringed topoi along which degreewise pullback inverts the
quasi-isomorphisms between K-flat complexes with flat terms, the derived pullback exists.  By
`hasResolutions_isKFlat` this is the whole of the resolving datum at that class.

`hmos` says that `f` is a morphism of ringed topoi in the sense of the source, and `hinv` is
the content of Tag 06YY, deferred in the spelling that file uses for it — which that file
assumes rather than proves: see the implementation notes. -/
theorem pullbackOnHomotopy_hasLeftDerivedFunctor_of_kFlat
    (hmos : f.u.IsMorphismOfSites Y.J X.J)
    (hinv : f.u.IsMorphismOfSites Y.J X.J → PullbackInvertsQuasiIso f (IsKFlat (Y := Y))) :
    (pullbackOnHomotopy f).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        (.up ℤ)) :=
  pullbackOnHomotopy_hasLeftDerivedFunctor f _ hasResolutions_isKFlat (hinv hmos)

variable [HasDerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
variable [(pullbackOnHomotopy f).HasLeftDerivedFunctor
  (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (.up ℤ))]

/-- **Stacks 07A6, from one hypothesis.**  For a morphism of ringed topoi along which
degreewise pullback inverts the quasi-isomorphisms between K-flat complexes with flat terms,
the derived pullback is left adjoint to the derived pushforward.  The resolving half of the
datum is Tag 06YS, so `hinv` is the only input left.

`hmos` says that `f` is a morphism of ringed topoi in the sense of the source, and `hinv` is
the content of Tag 06YY, deferred in the spelling that file uses for it — which that file
assumes rather than proves: see the implementation notes. -/
noncomputable def derivedPullbackPushforwardAdjunctionOfKFlat
    (hmos : f.u.IsMorphismOfSites Y.J X.J)
    (hinv : f.u.IsMorphismOfSites Y.J X.J → PullbackInvertsQuasiIso f (IsKFlat (Y := Y))) :
    derivedPullback f ⊣ derivedPushforward f :=
  derivedPullbackPushforwardAdjunction f _ hasResolutions_isKFlat (hinv hmos)

omit [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The unit of `derivedPullbackPushforwardAdjunctionOfKFlat` agrees with the ordinary
pullback--pushforward unit after applying the canonical comparison maps. -/
theorem derivedPullbackPushforwardAdjunctionOfKFlat_unit_fac
    (hmos : f.u.IsMorphismOfSites Y.J X.J)
    (hinv : f.u.IsMorphismOfSites Y.J X.J → PullbackInvertsQuasiIso f (IsKFlat (Y := Y)))
    (M : HomotopyCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (.up ℤ)) :
    (derivedPullbackPushforwardAdjunctionOfKFlat f hmos hinv).unit.app
          (DerivedCategory.Qh.obj M) ≫
        (derivedPushforward f).map ((derivedPullbackComparison f).app M) =
      DerivedCategory.Qh.map ((homotopyPullbackPushforwardAdjunction f).unit.app M) ≫
        (derivedPushforwardUnit f).app
          ((f.pullbackTopos.mapHomotopyCategory (.up ℤ)).obj M) :=
  derivedPullbackPushforwardAdjunction_unit_fac f _ hasResolutions_isKFlat (hinv hmos) M

omit [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The counit of `derivedPullbackPushforwardAdjunctionOfKFlat` agrees with the ordinary
pullback--pushforward counit after applying the canonical comparison maps. -/
theorem derivedPullbackPushforwardAdjunctionOfKFlat_counit_fac
    (hmos : f.u.IsMorphismOfSites Y.J X.J)
    (hinv : f.u.IsMorphismOfSites Y.J X.J → PullbackInvertsQuasiIso f (IsKFlat (Y := Y)))
    (K : HomotopyCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (.up ℤ)) :
    (derivedPullback f).map ((derivedPushforwardUnit f).app K) ≫
        (derivedPullbackPushforwardAdjunctionOfKFlat f hmos hinv).counit.app
          (DerivedCategory.Qh.obj K) =
      (derivedPullbackComparison f).app
          ((f.pushforwardTopos.mapHomotopyCategory (.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map
          ((homotopyPullbackPushforwardAdjunction f).counit.app K) :=
  derivedPullbackPushforwardAdjunction_counit_fac f _ hasResolutions_isKFlat (hinv hmos) K

end KFlatDatum

section Exact

/-- The class of all objects resolves every complex, by the identity. -/
theorem hasResolutions_top (Z : RingedTopos.{w, w, w})
    [Z.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [HasSheafify Z.J AddCommGrpCat.{w}]
    [Z.J.WEqualsLocallyBijective AddCommGrpCat.{w}] :
    ∀ M : HomotopyCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
        (.up ℤ),
      ∃ (K : HomotopyCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
          (.up ℤ))
        (_ : (⊤ : ObjectProperty
          (HomotopyCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
            (.up ℤ))) K) (s : K ⟶ M),
        HomotopyCategory.quasiIso (SheafOfModules.{w}
          (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) (.up ℤ) s :=
  fun M => ⟨M, trivial, 𝟙 M, MorphismProperty.id_mem _ _⟩

variable [PreservesFiniteLimits f.pullbackTopos] [PreservesFiniteColimits f.pullbackTopos]

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- An exact degreewise pullback inverts every quasi-isomorphism, so the class of all
objects is a resolving datum for it.  This exhibits the datum as satisfiable. -/
theorem pullbackInvertsQuasiIso_top : PullbackInvertsQuasiIso f ⊤ :=
  fun s hs _ _ => Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso _ _) _
    (f.pullbackTopos.quasiIso_mapHomotopyCategory_map (.up ℤ) s hs)

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- For a morphism of ringed topoi along which pullback is exact, the derived pullback
exists. -/
theorem pullbackOnHomotopy_hasLeftDerivedFunctor_of_exact :
    (pullbackOnHomotopy f).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        (.up ℤ)) :=
  pullbackOnHomotopy_hasLeftDerivedFunctor f ⊤ (hasResolutions_top Y)
    (pullbackInvertsQuasiIso_top f)

/-- For a morphism of ringed topoi along which pullback is exact, the derived pullback is
left adjoint to the derived pushforward.  This is the conclusion of Tag 07A6 for such a
morphism, with no resolving datum left over. -/
noncomputable def derivedPullbackPushforwardAdjunctionOfExact
    [HasDerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
    [(pullbackOnHomotopy f).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        (.up ℤ))] :
    derivedPullback f ⊣ derivedPushforward f :=
  derivedPullbackPushforwardAdjunction f ⊤ (hasResolutions_top Y)
    (pullbackInvertsQuasiIso_top f)

end Exact

end Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

end
