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
public import StacksFrontier.Homology.Injectives.Spaltenstein.Enlargement
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace

/-!
# The derived pullback is left adjoint to the derived pushforward

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces.  The unbounded derived
pushforward `Rf_*` is constructed here from K-injective resolutions, and shown to be right
adjoint to the unbounded derived pullback `Lf^*`, with the adjunction compatible with the
canonical comparison maps of the two derived functors.

The pushforward half is unconditional: sheaves of modules on a ringed space form a
Grothendieck abelian category, so every complex admits a quasi-isomorphism into a K-injective
one, and `Rf_*` exists and is computed by K-injective complexes.

The pullback half is relative to a *resolving datum* for `f^*`: a class `P` of objects of
`K(𝒪_Y)` such that every complex receives a quasi-isomorphism from one in `P`
(`HasResolutions`) and such that `f^*` carries quasi-isomorphisms between complexes in `P` to
isomorphisms of `D(𝒪_X)` (`PullbackInvertsQuasiIso`).  Such a datum produces `Lf^*` as a total
left derived functor, and makes the adjunction follow.  The intended class is the K-flat
complexes.

## Main definitions

* `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward` is `Rf_*`, with comparison
  `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardUnit`.
* `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback` is `Lf^*`, with comparison
  `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison`.
* `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.homotopyPullbackPushforwardAdjunction` is
  `K(f^*) ⊣ K(f_*)`.
* `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackPushforwardAdjunction` is the
  adjunction `Lf^* ⊣ Rf_*`.
* `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackPushforwardAdjunctionOfExact`
  is that adjunction for a morphism along which `f^*` is exact, where no resolving datum is left
  over.

## Main results

* `isRightDerivedFunctor_of_isIso_app_isKInjective`: a comparison invertible on
  the K-injective complexes exhibits its functor as a right derived functor.  This is the
  converse of the second half of Tag 070K.
* `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.pushforward_hasRightDerivedFunctor`: `Rf_*`
  exists, unconditionally.
* `isIso_derivedPushforwardUnit_app_of_isKInjective`: K-injective complexes
  compute `Rf_*`.
* `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.comp_isRightDerivedFunctor` and
  `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.comp_isLeftDerivedFunctor`:
  absoluteness of the two derived functors.
* `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackPushforwardAdjunction_unit_fac`
  and
  `derivedPullbackPushforwardAdjunction_counit_fac`: the compatibility of the
  derived unit and counit with the ordinary ones.

## Implementation notes

*The two derived categories are instance arguments.*  Every statement below that mentions a
derived category takes `[HasDerivedCategory.{w₁} (SheafOfModules.{u} (structureSheafRing X))]` and
`[HasDerivedCategory.{w₂} (SheafOfModules.{u} (structureSheafRing Y))]` as binders, with
independent morphism universes, rather than fixing a model by a file-level
`attribute [local instance] HasDerivedCategory.standard`.  Nothing in the argument needs the
standard model: the recognition criterion and the resolving-datum machinery are stated by
Mathlib and by `StacksFrontier.CategoryTheory.Localization.LeftDerivedByResolutions` at a general
`[HasDerivedCategory.{w} _]`, and the K-injective input `Stacks079N`
`.exists_functorial_quasiIso_isKInjective` mentions no derived category at all.  Keeping the
model free is what makes `Lf^* ⊣ Rf_*` usable at the locally small model of
`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean` — the only model at which `D(𝒪_X)` has
the direct sums that [Stacks, Tag 0A8G] needs, so the only model at which the compact-generation
statements of Tags 09IS and 0A9A have content; a statement proved for the standard model says
nothing about that one.  The standard-model form is recovered by instantiation, under a local
`HasDerivedCategory.standard` instance.

Three declarations stay model-free and must not acquire a binder:
`homotopyPullbackPushforwardAdjunction` and `HasResolutions`, which speak only of homotopy
categories, and `hasResolutions_top`, which is applied at a ringed space carrying no chosen
model.  The `omit` lines below keep the remaining statements at the one binder they use.

*Why the resolving datum is a hypothesis.*  Existence of `Lf^*` is the content of Tag 06YJ,
which the source cites rather than proves here, and it rests on the K-flat resolutions of Tag
06YS together with the exactness of `f^*` on K-flat complexes.  The second ingredient is not
available, so the datum is carried as a parameter; a single theorem of the shape of
`PullbackInvertsQuasiIso` at the K-flat class discharges it.

*One spelling for the quasi-isomorphisms.*  `HomotopyCategory.quasiIso` is written out at each
occurrence rather than abbreviated.  The class occurs both as the localizing class of
`DerivedCategory.Qh` and as the argument of `HasLeftDerivedFunctor`, and an abbreviation folded
over one of the two makes the instance arguments of `Functor.totalLeftDerived`, which precede
its explicit class argument, impossible to synthesize.

## References

* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 09T5](https://stacks.math.columbia.edu/tag/09T5)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

namespace Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe v₁ v₂ v₃ u₁ u₂ u₃ u w₁ w₂

/-- **Recognition of a right derived functor on the K-injective complexes.**  Let every complex
of `A` admit a quasi-isomorphism into a K-injective complex.  A functor `G : D ⥤ H` on a
localization `L` of `K(A)` at the quasi-isomorphisms, together with a comparison
`β : F ⟶ L ⋙ G` whose components at the K-injective complexes are invertible, is the right
derived functor of `F`.

This is the converse of the second conclusion of [Stacks, Tag 070K]. -/
theorem isRightDerivedFunctor_of_isIso_app_isKInjective
    {A : Type u₁} [Category.{v₁} A] [Abelian A] {H : Type u₂} [Category.{v₂} H]
    {D : Type u₃} [Category.{v₃} D]
    (F : HomotopyCategory A (ComplexShape.up ℤ) ⥤ H)
    (hA : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (g : K ⟶ I),
      I.IsKInjective ∧ QuasiIso g)
    (L : HomotopyCategory A (ComplexShape.up ℤ) ⥤ D)
    [L.IsLocalization (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (G : D ⥤ H) (β : F ⟶ L ⋙ G)
    (hβ : ∀ I : CochainComplex A ℤ, I.IsKInjective →
      IsIso (β.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I))) :
    G.IsRightDerivedFunctor β (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) := by
  have hpt := Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
    F hA
  have := hpt.1
  rw [Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc
    (F.totalRightDerived L (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)))
    (F.totalRightDerivedUnit L (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)))
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) G β, NatTrans.isIso_iff_isIso_app]
  intro Z
  have := Localization.essSurj L (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
  obtain ⟨K, hK⟩ := HomotopyCategory.quotient_obj_surjective (L.objPreimage Z)
  obtain ⟨I, g, hI, hg⟩ := hA K
  have hmem : HomotopyCategory.quasiIso A (ComplexShape.up ℤ)
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map g) := by
    rw [HomotopyCategory.quotient_map_mem_quasiIso_iff]; exact hg
  have e : L.obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I) ≅ Z :=
    (Localization.isoOfHom L (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) _ hmem).symm ≪≫
      (eqToIso (congrArg L.obj hK)).trans (L.objObjPreimageIso Z)
  rw [NatTrans.isIso_app_iff_of_iso _ e.symm]
  have := hpt.2 L
    (F.totalRightDerived L (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)))
    (F.totalRightDerivedUnit L (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))) I hI
  have := hβ I hI
  have : IsIso ((F.totalRightDerivedUnit L
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))).app
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I) ≫
      ((F.totalRightDerived L (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))).rightDerivedDesc
        (F.totalRightDerivedUnit L (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)))
        (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) G β).app
        (L.obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I))) := by
    rw [Functor.rightDerived_fac_app]; infer_instance
  exact IsIso.of_isIso_comp_left
    ((F.totalRightDerivedUnit L (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))).app
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)) _

/-- Every complex of modules on a ringed space admits a quasi-isomorphism into a K-injective
complex. -/
theorem exists_quasiIso_isKInjective (Z : RingedSpace.{u, u})
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing Z)) ℤ) :
    ∃ (I : CochainComplex (SheafOfModules.{u} (structureSheafRing Z)) ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f := by
  have := SheafOfModules.isGrothendieckAbelianU (structureSheafRing Z)
  obtain ⟨R⟩ := Stacks.Injectives.FunctorialEnlargement.exists_functorial_quasiIso_isKInjective.{u}
    (SheafOfModules.{u} (structureSheafRing Z))
  exact ⟨R.functor.obj K, R.inclusion.app K, R.isKInjective K, R.quasiIso K⟩

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  [HasDerivedCategory.{w₁} (SheafOfModules.{u} (structureSheafRing X))]
  [HasDerivedCategory.{w₂} (SheafOfModules.{u} (structureSheafRing Y))]

/-- Degreewise pushforward, followed by localization to the derived category. -/
noncomputable abbrev pushforwardToDerivedCategory :
    HomotopyCategory (SheafOfModules.{u} (structureSheafRing X)) (.up ℤ) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)) :=
  (modulePushforward f).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh

/-- K-injective resolutions compute the derived pushforward pointwise. -/
noncomputable instance pushforward_hasPointwiseRightDerivedFunctor :
    (pushforwardToDerivedCategory f).HasPointwiseRightDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (.up ℤ)) :=
  (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{
      u, w₂, u + 1, u + 1, u + 1, u + 1}
      (pushforwardToDerivedCategory f) (exists_quasiIso_isKInjective X)).1

/-- K-injective resolutions give the unbounded derived pushforward. -/
noncomputable instance pushforward_hasRightDerivedFunctor :
    (pushforwardToDerivedCategory f).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (.up ℤ)) :=
  Functor.hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor _ _

/-- The chosen unbounded derived pushforward `Rf_*`, the total right derived functor of
degreewise pushforward followed by localization. -/
noncomputable abbrev derivedPushforward :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)) :=
  (pushforwardToDerivedCategory f).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (.up ℤ))

/-- The canonical comparison from degreewise pushforward to the derived pushforward. -/
noncomputable abbrev derivedPushforwardUnit :
    pushforwardToDerivedCategory f ⟶ DerivedCategory.Qh ⋙ derivedPushforward f :=
  (pushforwardToDerivedCategory f).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (.up ℤ))

/-- A K-injective complex computes the derived pushforward: on it the canonical comparison
`f_* I ⟶ Rf_* I` is invertible. -/
theorem isIso_derivedPushforwardUnit_app_of_isKInjective
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) (hI : I.IsKInjective) :
    IsIso ((derivedPushforwardUnit f).app
      ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing X)) (.up ℤ)).obj I)) :=
  (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{
      u, w₂, w₁, u + 1, u + 1, u + 1}
      (pushforwardToDerivedCategory f) (exists_quasiIso_isKInjective X)).2
    DerivedCategory.Qh (derivedPushforward f) (derivedPushforwardUnit f) I hI

/-- Degreewise pullback, followed by localization to the derived category. -/
noncomputable abbrev pullbackOnHomotopy :
    HomotopyCategory (SheafOfModules.{u} (structureSheafRing Y)) (.up ℤ) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) :=
  (modulePullback f).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh

/-- The adjunction `K(f^*) ⊣ K(f_*)` on the unbounded homotopy categories, induced degreewise
by the adjunction `f^* ⊣ f_*` of Stacks 0096. -/
noncomputable abbrev homotopyPullbackPushforwardAdjunction :
    (modulePullback f).mapHomotopyCategory (.up ℤ) ⊣
      (modulePushforward f).mapHomotopyCategory (.up ℤ) :=
  CategoryTheory.Adjunction.mapHomotopyCategoryAdjunction
    (modulePullbackPushforwardAdjunction f) (.up ℤ)

section Pullback

variable (P : ObjectProperty (HomotopyCategory (SheafOfModules.{u} (structureSheafRing Y)) (.up ℤ)))

/-- The resolving property: every complex of `𝒪_Y`-modules receives a quasi-isomorphism from
one satisfying `P`. -/
abbrev HasResolutions (P : ObjectProperty
      (HomotopyCategory (SheafOfModules.{u} (structureSheafRing Y)) (.up ℤ))) : Prop :=
  ∀ M : HomotopyCategory (SheafOfModules.{u} (structureSheafRing Y)) (.up ℤ),
    ∃ (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing Y)) (.up ℤ)) (_ : P K)
        (s : K ⟶ M),
      HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y)) (.up ℤ) s

/-- The exactness property: degreewise pullback carries a quasi-isomorphism between complexes
satisfying `P` to an isomorphism of derived categories. -/
abbrev PullbackInvertsQuasiIso : Prop :=
  ∀ {K M : HomotopyCategory (SheafOfModules.{u} (structureSheafRing Y)) (.up ℤ)} (s : K ⟶ M),
    HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y)) (.up ℤ) s → P K → P M →
      IsIso ((pullbackOnHomotopy f).map s)

variable (hP : HasResolutions P) (hinv : PullbackInvertsQuasiIso f P)

omit [HasDerivedCategory.{w₂} (SheafOfModules.{u} (structureSheafRing Y))] in
include hP hinv in
/-- Resolutions by `P` compute the derived pullback pointwise. -/
theorem pullbackOnHomotopy_hasPointwiseLeftDerivedFunctor :
    (pullbackOnHomotopy f).HasPointwiseLeftDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y)) (.up ℤ)) :=
  LeftDerivedByResolutions.hasPointwiseLeftDerivedFunctor_of_resolutions
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y)) (.up ℤ)) P hP
    (pullbackOnHomotopy f) hinv

omit [HasDerivedCategory.{w₂} (SheafOfModules.{u} (structureSheafRing Y))] in
include hP hinv in
/-- Resolutions by `P` give the unbounded derived pullback. -/
theorem pullbackOnHomotopy_hasLeftDerivedFunctor :
    (pullbackOnHomotopy f).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y)) (.up ℤ)) :=
  have := pullbackOnHomotopy_hasPointwiseLeftDerivedFunctor f P hP hinv
  Functor.hasLeftDerivedFunctor_of_hasPointwiseLeftDerivedFunctor _ _

end Pullback

section

variable [(pullbackOnHomotopy f).HasLeftDerivedFunctor
  (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y)) (.up ℤ))]

/-- The derived pullback `Lf^* : D(𝒪_Y) ⥤ D(𝒪_X)`. -/
noncomputable abbrev derivedPullback :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) :=
  (pullbackOnHomotopy f).totalLeftDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y)) (.up ℤ))

/-- The canonical comparison from the derived pullback to degreewise pullback. -/
noncomputable abbrev derivedPullbackComparison :
    DerivedCategory.Qh ⋙ derivedPullback f ⟶ pullbackOnHomotopy f :=
  (pullbackOnHomotopy f).totalLeftDerivedCounit DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y)) (.up ℤ))

end

section Main

variable (P : ObjectProperty (HomotopyCategory (SheafOfModules.{u} (structureSheafRing Y)) (.up ℤ)))
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y)) (.up ℤ))]

/-- The derived pushforward stays a right derived functor after composing with the derived
pullback. -/
theorem comp_isRightDerivedFunctor :
    (derivedPushforward f ⋙ derivedPullback f).IsRightDerivedFunctor
      (Functor.whiskerRight (derivedPushforwardUnit f) (derivedPullback f) ≫
        (Functor.associator DerivedCategory.Qh (derivedPushforward f)
          (derivedPullback f)).hom)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (.up ℤ)) := by
  refine isRightDerivedFunctor_of_isIso_app_isKInjective.{
      u, w₁, w₁, u + 1, u + 1, u + 1}
    (pushforwardToDerivedCategory f ⋙ derivedPullback f) (exists_quasiIso_isKInjective X)
    DerivedCategory.Qh _ _ (fun I hI => ?_)
  have := isIso_derivedPushforwardUnit_app_of_isKInjective f I hI
  rw [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Category.comp_id]
  infer_instance

variable (hP : HasResolutions P) (hinv : PullbackInvertsQuasiIso f P)

include hP hinv in
/-- The derived pullback stays a left derived functor after composing with the derived
pushforward. -/
theorem comp_isLeftDerivedFunctor :
    (derivedPullback f ⋙ derivedPushforward f).IsLeftDerivedFunctor
      ((Functor.associator DerivedCategory.Qh (derivedPullback f)
          (derivedPushforward f)).inv ≫
        Functor.whiskerRight (derivedPullbackComparison f) (derivedPushforward f))
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y)) (.up ℤ)) := by
  refine LeftDerivedByResolutions.isLeftDerivedFunctor_of_isIso_on_resolutions
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y)) (.up ℤ)) P hP
    (pullbackOnHomotopy f ⋙ derivedPushforward f)
    (fun s hs hK hM => by
      have := hinv s hs hK hM
      change IsIso ((derivedPushforward f).map ((pullbackOnHomotopy f).map s))
      infer_instance)
    DerivedCategory.Qh _ _ (fun K hK => ?_)
  have := LeftDerivedByResolutions.isIso_app_of_resolutions
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y)) (.up ℤ)) P hP
    (pullbackOnHomotopy f) hinv DerivedCategory.Qh (derivedPullback f)
    (derivedPullbackComparison f) K hK
  rw [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_inv_app,
    Category.id_comp]
  infer_instance

include hP hinv in
/-- The adjunction `Lf^* ⊣ Rf_*` on the unbounded derived categories of sheaves of modules
over ringed spaces. -/
noncomputable def derivedPullbackPushforwardAdjunction :
    derivedPullback f ⊣ derivedPushforward f :=
  have := comp_isRightDerivedFunctor f
  have := comp_isLeftDerivedFunctor f P hP hinv
  (homotopyPullbackPushforwardAdjunction f).derived
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y)) (.up ℤ))
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (.up ℤ))
    (derivedPullbackComparison f) (derivedPushforwardUnit f)

include hP hinv in
/-- The derived unit agrees with the ordinary unit after applying the canonical comparison
maps. -/
theorem derivedPullbackPushforwardAdjunction_unit_fac
    (M : HomotopyCategory (SheafOfModules.{u} (structureSheafRing Y)) (.up ℤ)) :
    (derivedPullbackPushforwardAdjunction f P hP hinv).unit.app
          (DerivedCategory.Qh.obj M) ≫
        (derivedPushforward f).map ((derivedPullbackComparison f).app M) =
      DerivedCategory.Qh.map ((homotopyPullbackPushforwardAdjunction f).unit.app M) ≫
        (derivedPushforwardUnit f).app
          (((modulePullback f).mapHomotopyCategory (.up ℤ)).obj M) :=
  have := comp_isRightDerivedFunctor f
  have := comp_isLeftDerivedFunctor f P hP hinv
  (homotopyPullbackPushforwardAdjunction f).derivedη_fac_app
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y)) (.up ℤ))
    (derivedPullbackComparison f) (derivedPushforwardUnit f) M

include hP hinv in
/-- The derived counit agrees with the ordinary counit after applying the canonical comparison
maps. -/
theorem derivedPullbackPushforwardAdjunction_counit_fac
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X)) (.up ℤ)) :
    (derivedPullback f).map ((derivedPushforwardUnit f).app K) ≫
        (derivedPullbackPushforwardAdjunction f P hP hinv).counit.app
          (DerivedCategory.Qh.obj K) =
      (derivedPullbackComparison f).app
          (((modulePushforward f).mapHomotopyCategory (.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map
          ((homotopyPullbackPushforwardAdjunction f).counit.app K) :=
  have := comp_isRightDerivedFunctor f
  have := comp_isLeftDerivedFunctor f P hP hinv
  (homotopyPullbackPushforwardAdjunction f).derivedε_fac_app
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (.up ℤ))
    (derivedPullbackComparison f) (derivedPushforwardUnit f) K



end Main

section Exact

variable [PreservesFiniteLimits (modulePullback f)]
  [PreservesFiniteColimits (modulePullback f)]

/-- The class of all objects resolves every complex, by the identity. -/
theorem hasResolutions_top (Z : RingedSpace.{u, u}) :
    HasResolutions (⊤ : ObjectProperty
      (HomotopyCategory (SheafOfModules.{u} (structureSheafRing Z)) (.up ℤ))) :=
  fun M => ⟨M, trivial, 𝟙 M, MorphismProperty.id_mem _ _⟩

/-- An exact degreewise pullback inverts every quasi-isomorphism, so the class of all objects
is a resolving datum for it. -/
theorem pullbackInvertsQuasiIso_top :
    PullbackInvertsQuasiIso f ⊤ :=
  fun _s hs _ _ =>
    Stacks.DerivedFunctor.HigherDerivedOfExact.mapHomotopyCategory_inverts_quasiIso (modulePullback
      f) _ hs

/-- For a morphism of ringed spaces along which pullback is exact, the derived pullback
exists. -/
theorem pullbackOnHomotopy_hasLeftDerivedFunctor_of_exact :
    (pullbackOnHomotopy f).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y)) (.up ℤ)) :=
  pullbackOnHomotopy_hasLeftDerivedFunctor f ⊤ (hasResolutions_top Y)
    (pullbackInvertsQuasiIso_top f)

/-- For a morphism of ringed spaces along which pullback is exact, the derived pullback is
left adjoint to the derived pushforward.  This is the conclusion of Tag 079W for such a
morphism, with no resolving datum left over. -/
noncomputable def derivedPullbackPushforwardAdjunctionOfExact
    [(pullbackOnHomotopy f).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y)) (.up ℤ))] :
    derivedPullback f ⊣ derivedPushforward f :=
  derivedPullbackPushforwardAdjunction f ⊤ (hasResolutions_top Y)
    (pullbackInvertsQuasiIso_top f)

end Exact

end Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

end
