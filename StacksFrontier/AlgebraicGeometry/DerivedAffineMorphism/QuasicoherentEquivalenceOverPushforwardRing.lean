module

public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowNaturalTransformations
public import StacksFrontier.AlgebraicGeometry.AffineQcohUnit.Equivalence
public import StacksFrontier.AlgebraicGeometry.DerivedAffineMorphism.PushforwardOverRingQuasiCoherent
public import StacksFrontier.AlgebraicGeometry.DerivedAffineMorphism.QuasicoherentConservativeOverPushforwardRing
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.AffinePushforwardBounds
public import StacksFrontier.AlgebraicGeometry.QcohOverAlgebra.RestrictScalars
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CohomologicalDescent.UnitAndCounitIsomorphisms
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Triangulated

/-!
# `Φ` is an equivalence `D_QCoh(𝒪_X) ⥤ D_QCoh(f_* 𝒪_X)`

Let `f : X ⟶ S` be an affine morphism of schemes, let
`g : (X, 𝒪_X) ⟶ (S, f_* 𝒪_X)` be the morphism of ringed spaces of
`StacksFrontier/AlgebraicGeometry/DerivedAffineMorphism/RingedSpaceOverPushforwardRing.lean` and let
`Φ = Rg_* : D(𝒪_X) ⥤ D(f_* 𝒪_X)` be the functor of [Stacks, Tag 0AVW].  This file carries out
the second half of the source's proof of that tag: the unit and the counit of the adjunction
`Lg^* ⊣ Φ` are invertible on the subcategories of objects with quasi-coherent cohomology, so `Φ`
restricts to an **equivalence** `D_QCoh(𝒪_X) ⥤ D_QCoh(f_* 𝒪_X)` with quasi-inverse `Lg^*`.

The first half — that `g` is flat, that `g^*` is exact, the adjunction `Lg^* ⊣ Φ` and that `Lg^*`
preserves `D_QCoh` — is
`StacksFrontier/AlgebraicGeometry/DerivedAffineMorphism/FlatOverPushforwardRing.lean`.

## The argument

*The unit on complexes of quasi-coherent modules.*  The derived unit at an object represented by
a complex `N` of `f_* 𝒪_X`-modules factors, by
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackPushforwardAdjunction_unit_fac`,
through the degreewise unit of `g^* ⊣ g_*` at `N` and the comparison `g_*(g^*N) ⟶ Rg_*(g^*N)`.
When `N` is degreewise quasi-coherent all three correcting maps are invertible: the degreewise
unit by [Stacks, Tag 01SB], the comparison of the derived pullback because `g^*` is exact, and the
comparison of the derived pushforward by [Stacks, Tag 0G9N] for an affine morphism over `f_* 𝒪_X`
(`isIso_derivedPushforwardOverRingUnit_app_of_isAffineHom`), `g^*N` being degreewise quasi-coherent
by [Stacks, Tag 01BG].

*The counit on a single quasi-coherent sheaf.*  A quasi-coherent `𝒪_X`-module `M` is `g^*` of the
quasi-coherent `f_* 𝒪_X`-module `g_*M`, by the invertible counit of [Stacks, Tag 01SB]; and the
unit being invertible at `(g_*M)[0]` makes the counit invertible at `Lg^*((g_*M)[0]) ≅ M[0]`.

*The counit on bounded below objects.*  `CategoryTheory.NatTrans.isIso_app_of_isGE`: both `𝟭` and
`Lg^* ⋙ Φ` are exact, commute with the shift and preserve `D^{≥ n}` — the latter because `Lg^*` is
degreewise and `Φ` is a right adjoint of a functor preserving `D^{≤ n}`.

*The counit on all of `D_QCoh(𝒪_X)`.*  Fix a degree `j` and truncate at `-n ≤ j`.  The truncation
map is invertible on `H^j`; the counit at the truncation is invertible by the previous step; and
`Φ` of the truncation map is invertible on `H^j`, because `Rf_*` of it is — part (2) of
[Stacks, Tag 08D4] for an affine morphism — and restriction of scalars along `𝒪_S ⟶ f_* 𝒪_X`
reflects isomorphisms.  Applying `H^j ∘ Lg^* = g^* ∘ H^j` and reading the naturality square of the
counit gives the claim in degree `j`.

*The unit on all of `D_QCoh(f_* 𝒪_X)`, and the equivalence.*  By the triangle identity `Lg^*` of
the unit at `M` is invertible, which degreewise says that `g^*H^j` of it is; and `g^*` reflects
isomorphisms between quasi-coherent modules, because the unit of [Stacks, Tag 01SB] is invertible
there.  `Φ` is then fully faithful on `D_QCoh(𝒪_X)` ([Stacks, Tag 0D7R]) and essentially
surjective by the invertible unit, hence an equivalence.

## Main definitions

All in the namespace `Stacks.AlgebraicGeometry.DerivedAffinePushforward`.

* `derivedPullbackOverRingCompHomologyFunctorIso` — `H^i(Lg^* -) ≅ g^*H^i(-)`, **naturally**; the
  objectwise form is `homologyDerivedPullbackOverRingIso`.
* `derivedQuasicoherentScalarRestriction` — the functor `D_QCoh(f_* 𝒪_X) ⥤ D_QCoh(𝒪_S)` induced by
  restriction of scalars, which is the second functor named in the statement of the tag.
* `derivedQuasicoherentPushforwardAtModel` — `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_S)`.
* `derivedQuasicoherentPushforwardOverRingCompScalarRestrictionIso` — the factorisation of `Rf_*`
  through `D_QCoh(f_* 𝒪_X)`, read on the quasi-coherent subcategories.

## Main results

* `isIso_derivedCounitOverRing_app_of_isQuasicoherent` — **the counit `Lg^*ΦK ⟶ K` is invertible
  for every `K` of `D_QCoh(𝒪_X)`.**
* `isIso_derivedUnitOverRing_app_of_isQuasicoherent` — **the unit `M ⟶ ΦLg^*M` is invertible for
  every `M` of `D_QCoh(f_* 𝒪_X)`.**
* `isEquivalence_derivedQuasicoherentPushforwardOverRing` — **`Φ : D_QCoh(𝒪_X) ⥤ D_QCoh(f_* 𝒪_X)`
  is an equivalence.**
* `isEquivalence_and_factorisation_derivedQuasicoherentPushforwardOverRing` — **[Stacks, Tag 0AVW]
  in one statement**: that equivalence together with the factorisation of `Rf_*` through it.

## Implementation notes

*The model of the derived categories is pinned from `isGE_derivedPushforwardOverRing_obj` on.*
Two inputs are available only at `CategoryTheory.HasDerivedCategory.standard`: part (2) of
[Stacks, Tag 08D4] for an affine morphism
(`AlgebraicGeometry.isIso_homologyFunctor_map_derivedPushforward_truncGEπ`), and the exactness of
the derived pullback along a morphism of ringed spaces together with its commutation with the
shift (`Stacks.Cohomology.KFlatDerivedPullback.derivedPullback_commShift` and
`derivedPullback_isTriangulated`).  The statements that use them are therefore read there as well,
by `attribute [local instance 10000] HasDerivedCategory.standard` — at priority `10000` because
the import closure contains the locally small instance `SheafOfModules.hasDerivedCategory`, which
instance search would otherwise prefer.  Everything before that section is stated at an arbitrary
chosen model.

*Why `derivedQuasicoherentPushforwardAtModel` is not
`AlgebraicGeometry.derivedQuasicoherentPushforward`.*  The latter is the same lift of `Rf_*` with
the model fixed at the locally small one, and `HasDerivedCategory` carries the localized category
as data, so it cannot appear beside the equivalence clause, which is pinned to the standard model.
The definition below is that functor with the model as a binder; the two agree at the locally
small model.

*Instance search does not cross the two spellings of `𝒪_X`.*
`AlgebraicGeometry.Scheme.ringCatSheaf` is a `TopCat.Sheaf` and
`Stacks.Cohomology.SpectralLimit.SheafedSpaceLimit.structureSheafRing` of the same space is a
`CategoryTheory.Sheaf` for the induced topology; the two are equal by `rfl`, but a goal mentioning
the first is not type-correct at `implicit` transparency against the second, so synthesis of an
instance registered for `derivedPullback g` fails against `derivedPullbackOverRing f` with a type
mismatch rather than with a missing instance.  The three instances that must cross — exactness, the
commutation with the shift, and the preservation of zero morphisms — are therefore supplied by
`inferInstanceAs` written at the ringed-space spelling.

## References

* [Stacks Project, Tag 0AVW](https://stacks.math.columbia.edu/tag/0AVW)
* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
* [Stacks Project, Tag 01SB](https://stacks.math.columbia.edu/tag/01SB)
* [Stacks Project, Tag 08D4](https://stacks.math.columbia.edu/tag/08D4)
* [Stacks Project, Tag 0D7R](https://stacks.math.columbia.edu/tag/0D7R)
* [Stacks Project, Tag 0G9N](https://stacks.math.columbia.edu/tag/0G9N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.AffineQcohPushforward
open Stacks.AlgebraicGeometry.AffineQcohEquivalence
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe w u

namespace Stacks.AlgebraicGeometry.DerivedAffinePushforward

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-! ### `g^*` reflects isomorphisms between quasi-coherent modules -/

/-- **`g^*` reflects isomorphisms between quasi-coherent `f_* 𝒪_X`-modules.**  A map `φ` of
quasi-coherent modules with `g^*φ` invertible is itself invertible.

The unit of [Stacks, Tag 01SB] is invertible at both ends, and its naturality square writes `φ` as
a composite of `g_*g^*φ` with two invertible maps. -/
theorem isIso_of_isIso_pullbackModules_map [IsAffineHom f]
    {G G' : SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf)}
    (hG : G.IsQuasicoherent) (hG' : G'.IsQuasicoherent) (φ : G ⟶ G')
    (h : IsIso ((pullbackModules f).map φ)) : IsIso φ := by
  have h1 := Stacks.AlgebraicGeometry.AffineQcohUnit.isIso_unit_app_of_isQuasicoherent f G hG
  have h2 := Stacks.AlgebraicGeometry.AffineQcohUnit.isIso_unit_app_of_isQuasicoherent f G' hG'
  have h3 : IsIso ((pullbackModules f ⋙ pushforwardModules.{u} f.base X.ringCatSheaf).map φ) := by
    have := h
    exact inferInstanceAs (IsIso ((pushforwardModules.{u} f.base X.ringCatSheaf).map
      ((pullbackModules f).map φ)))
  have hn : φ ≫ (pullbackPushforwardAdjunction f).unit.app G' =
      (pullbackPushforwardAdjunction f).unit.app G ≫
        (pullbackModules f ⋙ pushforwardModules.{u} f.base X.ringCatSheaf).map φ :=
    (pullbackPushforwardAdjunction f).unit.naturality φ
  have hcomp : IsIso (φ ≫ (pullbackPushforwardAdjunction f).unit.app G') := by
    rw [hn]; infer_instance
  exact IsIso.of_isIso_comp_right φ ((pullbackPushforwardAdjunction f).unit.app G')

/-! ### The zero module and single complexes over `f_* 𝒪_X` -/

/-- A zero module over `f_* 𝒪_X` is quasi-coherent: the free module on the empty index set is a
zero object and is quasi-coherent. -/
theorem containsZero_isQuasicoherent_pushforwardRing :
    (SheafOfModules.isQuasicoherent (pushforwardRing f.base X.ringCatSheaf)).ContainsZero := by
  refine ⟨SheafOfModules.free (R := pushforwardRing f.base X.ringCatSheaf) (PEmpty : Type u),
    ?_, inferInstance⟩
  rw [IsZero.iff_id_eq_zero]
  exact Sigma.hom_ext _ _ (fun n ↦ n.elim)

/-- Every term of the complex `N[0]` concentrated in degree zero is quasi-coherent when the
`f_* 𝒪_X`-module `N` is: the term in degree zero is `N`, and the others are zero objects. -/
theorem isQuasicoherent_single_obj_X_pushforwardRing
    (N : SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf))
    (hN : N.IsQuasicoherent) (n : ℤ) :
    (((CochainComplex.singleFunctor
      (SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf)) 0).obj N).X
        n).IsQuasicoherent := by
  have hP := containsZero_isQuasicoherent_pushforwardRing f
  by_cases h : n = 0
  · subst h
    exact (SheafOfModules.isQuasicoherent (pushforwardRing f.base X.ringCatSheaf)).prop_of_iso
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 N).symm hN
  · exact (SheafOfModules.isQuasicoherent (pushforwardRing f.base X.ringCatSheaf)).prop_of_iso
      (HomologicalComplex.isZero_single_obj_X
        (ComplexShape.up ℤ) 0 N n h).isoZero.symm (ObjectProperty.prop_zero _)

/-- If `H^i(M)` vanishes then so does `H^i(g^*M)`, `g^*` being applied degreewise. -/
private theorem isZero_homologyFunctor_mapDerivedCategory_obj [IsAffineHom f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} X.ringCatSheaf)]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf))] (i : ℤ)
    (M : DerivedCategory (SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf)))
    (h : IsZero ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf)) i).obj M)) :
    IsZero ((DerivedCategory.homologyFunctor (SheafOfModules.{u} X.ringCatSheaf) i).obj
      ((RingedSpaceModuleAdjunction.modulePullback
        (toPushforwardStructureSpace f)).mapDerivedCategory.obj M)) :=
  ((RingedSpaceModuleAdjunction.modulePullback (toPushforwardStructureSpace f)).map_isZero
    h).of_iso
    (((RingedSpaceModuleAdjunction.modulePullback
      (toPushforwardStructureSpace f)).mapDerivedCategoryCompHomologyFunctorIso i).app M)

section Derived

variable [IsAffineHom f]
  [HasDerivedCategory.{w} (SheafOfModules.{u} X.ringCatSheaf)]
  [HasDerivedCategory.{w} (SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf))]
  [HasDerivedCategory.{w} (SheafOfModules.{u} S.ringCatSheaf)]

/-! ### `H^i ∘ Lg^* ≅ g^* ∘ H^i`, naturally -/

/-- **`H^i(Lg^*M) ≅ g^*H^i(M)`, naturally in `M`.**  `Lg^*` is the functor `g^*` induces on
derived categories, and an exact functor's induced functor commutes with cohomology; both
identifications are natural isomorphisms, so this is their composite.  The objectwise form is
`homologyDerivedPullbackOverRingIso`. -/
def derivedPullbackOverRingCompHomologyFunctorIso (i : ℤ) :
    derivedPullbackOverRing.{w} f ⋙
        DerivedCategory.homologyFunctor (SheafOfModules.{u} X.ringCatSheaf) i ≅
      DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf)) i ⋙ pullbackModules f :=
  Functor.isoWhiskerRight (derivedPullbackOverRingIsoMapDerivedCategory.{w} f).symm
      (DerivedCategory.homologyFunctor (SheafOfModules.{u} X.ringCatSheaf) i) ≪≫
    (RingedSpaceModuleAdjunction.modulePullback
      (toPushforwardStructureSpace f)).mapDerivedCategoryCompHomologyFunctorIso i

omit [HasDerivedCategory.{w} (SheafOfModules.{u} S.ringCatSheaf)] in
/-- **`H^i(Lg^*β)` is invertible exactly when `g^*H^i(β)` is**, the two being the same map under
`derivedPullbackOverRingCompHomologyFunctorIso`. -/
theorem isIso_homologyFunctor_map_derivedPullbackOverRing_map_iff (i : ℤ)
    {M N : DerivedCategory (SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf))}
    (β : M ⟶ N) :
    IsIso ((DerivedCategory.homologyFunctor (SheafOfModules.{u} X.ringCatSheaf) i).map
        ((derivedPullbackOverRing.{w} f).map β)) ↔
      IsIso ((pullbackModules f).map ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf)) i).map β)) :=
  NatIso.isIso_map_iff (derivedPullbackOverRingCompHomologyFunctorIso.{w} f i) β

/-! ### The derived unit on a complex of quasi-coherent modules -/

omit [HasDerivedCategory.{w} (SheafOfModules.{u} S.ringCatSheaf)] in
/-- The comparison `Lg^*(QhN) ⟶ Qh(g^*N)` of the derived pullback is invertible at every object:
`g^*` is exact, so the class of all objects is a resolving datum for it, and the comparison of a
left derived functor is invertible on a resolving class. -/
theorem isIso_derivedPullbackComparison_app_toPushforwardStructureSpace
    (N : HomotopyCategory
      (SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf)) (ComplexShape.up ℤ)) :
    IsIso ((derivedPullbackComparison (toPushforwardStructureSpace f)).app N) :=
  LeftDerivedByResolutions.isIso_app_of_resolutions
    (HomotopyCategory.quasiIso (SheafOfModules.{u}
      (structureSheafRing (pushforwardStructureSpace f))) (ComplexShape.up ℤ)) ⊤
    (hasResolutions_top _) (pullbackOnHomotopy (toPushforwardStructureSpace f))
    (pullbackInvertsQuasiIso_top _) DerivedCategory.Qh
    (derivedPullback (toPushforwardStructureSpace f))
    (derivedPullbackComparison (toPushforwardStructureSpace f)) N trivial

omit [HasDerivedCategory.{w} (SheafOfModules.{u} S.ringCatSheaf)] in
/-- **The unit of `Lg^* ⊣ Φ` is the degreewise unit of `g^* ⊣ g_*`, corrected by the two
comparison maps.**  This is
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackPushforwardAdjunction_unit_fac`
read at the resolving datum exactness supplies, which is the one
`derivedPullbackPushforwardAdjunctionOverRing` is built from. -/
theorem derivedPullbackPushforwardAdjunctionOverRing_unit_fac
    (N : HomotopyCategory
      (SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf)) (ComplexShape.up ℤ)) :
    (derivedPullbackPushforwardAdjunctionOverRing.{w} f).unit.app
          (DerivedCategory.Qh.obj N) ≫
        (derivedPushforwardOverRing.{w} f).map
          ((derivedPullbackComparison (toPushforwardStructureSpace f)).app N) =
      DerivedCategory.Qh.map
          ((homotopyPullbackPushforwardAdjunction (toPushforwardStructureSpace f)).unit.app N) ≫
        (derivedPushforwardUnit (toPushforwardStructureSpace f)).app
          (((RingedSpaceModuleAdjunction.modulePullback
            (toPushforwardStructureSpace f)).mapHomotopyCategory (ComplexShape.up ℤ)).obj N) :=
  derivedPullbackPushforwardAdjunction_unit_fac (toPushforwardStructureSpace f) ⊤
    (hasResolutions_top _) (pullbackInvertsQuasiIso_top _) N

omit [HasDerivedCategory.{w} (SheafOfModules.{u} S.ringCatSheaf)] in
/-- The derived unit at `QhN` is invertible as soon as the degreewise unit at `N` and the
comparison `g_*(g^*N) ⟶ Rg_*(g^*N)` are: the factorisation
`derivedPullbackPushforwardAdjunctionOverRing_unit_fac` then has an invertible right-hand side,
and its remaining left-hand factor is invertible because `g^*` is exact. -/
theorem isIso_derivedUnitOverRing_app_Qh_of_isIso
    (N : HomotopyCategory
      (SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf)) (ComplexShape.up ℤ))
    (h1 : IsIso ((homotopyPullbackPushforwardAdjunction
      (toPushforwardStructureSpace f)).unit.app N))
    (h2 : IsIso ((derivedPushforwardUnit (toPushforwardStructureSpace f)).app
      (((RingedSpaceModuleAdjunction.modulePullback
        (toPushforwardStructureSpace f)).mapHomotopyCategory (ComplexShape.up ℤ)).obj N))) :
    IsIso ((derivedPullbackPushforwardAdjunctionOverRing.{w} f).unit.app
      (DerivedCategory.Qh.obj N)) := by
  have hg : IsIso ((derivedPushforwardOverRing.{w} f).map
      ((derivedPullbackComparison (toPushforwardStructureSpace f)).app N)) :=
    ((derivedPushforwardOverRing.{w} f).mapIso (@asIso _ _ _ _ _
      (isIso_derivedPullbackComparison_app_toPushforwardStructureSpace.{w} f N))).isIso_hom
  have hkey : IsIso ((derivedPullbackPushforwardAdjunctionOverRing.{w} f).unit.app
      (DerivedCategory.Qh.obj N) ≫ (derivedPushforwardOverRing.{w} f).map
        ((derivedPullbackComparison (toPushforwardStructureSpace f)).app N)) := by
    rw [derivedPullbackPushforwardAdjunctionOverRing_unit_fac.{w} f N]
    exact IsIso.comp_isIso' (DerivedCategory.Qh.mapIso (@asIso _ _ _ _ _ h1)).isIso_hom h2
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ hg hkey

/-- **The derived unit is invertible at a complex of quasi-coherent `f_* 𝒪_X`-modules** — no
boundedness assumed.  The degreewise unit is invertible because the unit of [Stacks, Tag 01SB] is
invertible at a quasi-coherent module, and the comparison of the derived pushforward because
`g^*N` is again degreewise quasi-coherent, which is [Stacks, Tag 0G9N] for an affine morphism over
`f_* 𝒪_X`. -/
theorem isIso_derivedUnitOverRing_app_Qh_of_isQuasicoherent
    (N : CochainComplex (SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf)) ℤ)
    (hN : ∀ n : ℤ, (N.X n).IsQuasicoherent) :
    IsIso ((derivedPullbackPushforwardAdjunctionOverRing.{w} f).unit.app
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient
        (SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf))
          (ComplexShape.up ℤ)).obj N))) := by
  refine isIso_derivedUnitOverRing_app_Qh_of_isIso.{w} f _ ?_ ?_
  · have hcomp : ∀ n : ℤ, IsIso (((Adjunction.mapHomologicalComplexAdjunction
        (RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction
          (toPushforwardStructureSpace f)) (ComplexShape.up ℤ)).unit.app N).f n) := fun n => by
      have := Stacks.AlgebraicGeometry.AffineQcohUnit.isIso_unit_app_of_isQuasicoherent f _ (hN n)
      exact inferInstanceAs (IsIso ((pullbackPushforwardAdjunction f).unit.app (N.X n)))
    exact ((HomotopyCategory.quotient
      (SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf)) (ComplexShape.up ℤ)).mapIso
      (@asIso _ _ _ _ _ (@HomologicalComplex.Hom.isIso_of_components _ _ _ _ _ _ _
        ((Adjunction.mapHomologicalComplexAdjunction
          (RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction
            (toPushforwardStructureSpace f)) (ComplexShape.up ℤ)).unit.app N) hcomp))).isIso_hom
  · have := isIso_derivedPushforwardOverRingUnit_app_of_isAffineHom.{w} f
      (((RingedSpaceModuleAdjunction.modulePullback
        (toPushforwardStructureSpace f)).mapHomologicalComplex (ComplexShape.up ℤ)).obj N)
      (fun n => isQuasicoherent_pullbackModules f _ (hN n))
    exact inferInstanceAs (IsIso ((derivedPushforwardOverRingUnit.{w} f).app
      ((HomotopyCategory.quotient (SheafOfModules.{u} X.ringCatSheaf) (ComplexShape.up ℤ)).obj
        (((RingedSpaceModuleAdjunction.modulePullback
          (toPushforwardStructureSpace f)).mapHomologicalComplex (ComplexShape.up ℤ)).obj N))))

/-! ### The unit and the counit at a module placed in degree zero -/

/-- **The derived unit is invertible at a quasi-coherent `f_* 𝒪_X`-module placed in degree
zero**: that object is represented by the complex `N[0]`, which is degreewise quasi-coherent. -/
theorem isIso_derivedUnitOverRing_app_singleFunctor_of_isQuasicoherent
    (N : SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf)) (hN : N.IsQuasicoherent) :
    IsIso ((derivedPullbackPushforwardAdjunctionOverRing.{w} f).unit.app
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf)) 0).obj N)) := by
  have :=
    (derivedPullbackPushforwardAdjunctionOverRing.{w} f).isClosedUnderIsomorphisms_unitIsIso
  refine (derivedPullbackPushforwardAdjunctionOverRing.{w} f).unitIsIso.prop_of_iso
    (((DerivedCategory.quotientCompQhIso
      (SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf))).app
        ((CochainComplex.singleFunctor
          (SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf)) 0).obj N)) ≪≫
      ((DerivedCategory.singleFunctorIsoCompQ
        (SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf)) 0).app N).symm) ?_
  exact isIso_derivedUnitOverRing_app_Qh_of_isQuasicoherent.{w} f _
    (isQuasicoherent_single_obj_X_pushforwardRing f N hN)

/-- **`Lg^*(N[0]) ≅ (g^*N)[0]`**: `Lg^*` is the functor `g^*` induces on derived categories, and
an exact functor commutes with placing a module in a single degree. -/
def derivedPullbackOverRingSingleFunctorObjIso
    (N : SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf)) :
    (derivedPullbackOverRing.{w} f).obj ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf)) 0).obj N) ≅
      (DerivedCategory.singleFunctor (SheafOfModules.{u} X.ringCatSheaf) 0).obj
        ((pullbackModules f).obj N) :=
  ((derivedPullbackOverRingIsoMapDerivedCategory.{w} f).app
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf)) 0).obj N)).symm ≪≫
    ((RingedSpaceModuleAdjunction.modulePullback
      (toPushforwardStructureSpace f)).mapDerivedCategorySingleFunctor 0).app N

/-- **The derived counit is invertible at a quasi-coherent `𝒪_X`-module `M` placed in degree
zero.**  The counit of [Stacks, Tag 01SB] exhibits `M` as `g^*(g_*M)` with `g_*M` quasi-coherent,
so `M[0]` is `Lg^*((g_*M)[0])`; and the unit being invertible at `(g_*M)[0]` makes the counit
invertible there. -/
theorem isIso_derivedCounitOverRing_app_singleFunctor_of_isQuasicoherent
    (M : SheafOfModules.{u} X.ringCatSheaf) (hM : M.IsQuasicoherent) :
    IsIso ((derivedPullbackPushforwardAdjunctionOverRing.{w} f).counit.app
      ((DerivedCategory.singleFunctor (SheafOfModules.{u} X.ringCatSheaf) 0).obj M)) := by
  have :=
    (derivedPullbackPushforwardAdjunctionOverRing.{w} f).isClosedUnderIsomorphisms_counitIsIso
  have hc := Stacks.AlgebraicGeometry.PushforwardColimits.isIso_counit_app_of_isQuasicoherent
    f M hM
  refine (derivedPullbackPushforwardAdjunctionOverRing.{w} f).counitIsIso.prop_of_iso
    (derivedPullbackOverRingSingleFunctorObjIso.{w} f
        ((pushforwardModules.{u} f.base X.ringCatSheaf).obj M) ≪≫
      (DerivedCategory.singleFunctor (SheafOfModules.{u} X.ringCatSheaf) 0).mapIso
        (@asIso _ _ _ _ _ hc)) ?_
  exact (derivedPullbackPushforwardAdjunctionOverRing.{w} f).isIso_counit_app_obj_of_isIso_unit_app
    _ (isIso_derivedUnitOverRing_app_singleFunctor_of_isQuasicoherent.{w} f _
      (Stacks.AlgebraicGeometry.QcohLimits.affinePushforward_isQuasicoherent f M hM))

/-! ### `Lg^*` preserves boundedness in both directions -/

omit [HasDerivedCategory.{w} (SheafOfModules.{u} S.ringCatSheaf)] in
/-- **`Lg^*` preserves boundedness below**: it is degreewise `g^*`, which is exact, and an exact
functor commutes with cohomology. -/
theorem isGE_derivedPullbackOverRing_obj (M : DerivedCategory
    (SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf))) (n : ℤ) (hM : M.IsGE n) :
    ((derivedPullbackOverRing.{w} f).obj M).IsGE n := by
  have := hM
  have hmap : ((RingedSpaceModuleAdjunction.modulePullback
      (toPushforwardStructureSpace f)).mapDerivedCategory.obj M).IsGE n := by
    rw [DerivedCategory.isGE_iff]
    intro i hi
    exact isZero_homologyFunctor_mapDerivedCategory_obj f i M
      (DerivedCategory.isZero_of_isGE M n i hi)
  exact DerivedCategory.TStructure.t.isGE_of_iso
    ((derivedPullbackOverRingIsoMapDerivedCategory.{w} f).app M) n

omit [HasDerivedCategory.{w} (SheafOfModules.{u} S.ringCatSheaf)] in
/-- **`Lg^*` preserves boundedness above**, by the same argument. -/
theorem isLE_derivedPullbackOverRing_obj (M : DerivedCategory
    (SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf))) (n : ℤ) (hM : M.IsLE n) :
    ((derivedPullbackOverRing.{w} f).obj M).IsLE n := by
  have := hM
  have hmap : ((RingedSpaceModuleAdjunction.modulePullback
      (toPushforwardStructureSpace f)).mapDerivedCategory.obj M).IsLE n := by
    rw [DerivedCategory.isLE_iff]
    intro i hi
    exact isZero_homologyFunctor_mapDerivedCategory_obj f i M
      (DerivedCategory.isZero_of_isLE M n i hi)
  exact DerivedCategory.TStructure.t.isLE_of_iso
    ((derivedPullbackOverRingIsoMapDerivedCategory.{w} f).app M) n

/-! ### The two functors `D_QCoh(f_* 𝒪_X) ⥤ D_QCoh(𝒪_S)` and `D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_S)` -/

/-- **The functor `D_QCoh(f_* 𝒪_X) ⥤ D_QCoh(𝒪_S)` induced by restriction of scalars**, the second
functor named in the statement of [Stacks, Tag 0AVW].  It exists because restriction of scalars is
exact, so it commutes with cohomology, and an `f_* 𝒪_X`-module is quasi-coherent over `𝒪_S` when
it is over `f_* 𝒪_X`, which is the second assertion of [Stacks, Tag 01SB]. -/
def derivedQuasicoherentScalarRestriction :
    (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent
        (pushforwardRing f.base X.ringCatSheaf))).FullSubcategory ⥤
      (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherent S.ringCatSheaf)).FullSubcategory :=
  ObjectProperty.lift _
    (ObjectProperty.ι (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent
        (pushforwardRing f.base X.ringCatSheaf))) ⋙ (scalarRestriction f).mapDerivedCategory)
    (fun M i => (SheafOfModules.isQuasicoherent S.ringCatSheaf).prop_of_iso
      (((scalarRestriction f).mapDerivedCategoryCompHomologyFunctorIso i).app M.obj).symm
      ((Stacks.AlgebraicGeometry.QcohLimits.affine_isQuasicoherent_restrictScalars_iff
        f _).2 (M.property i)))

/-- **`Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_S)`**, at an arbitrary chosen model of the derived
categories.  This is `AlgebraicGeometry.derivedQuasicoherentPushforward` with the model a binder
rather than fixed at the locally small one; see the implementation notes for why the fixed model
cannot be used beside the equivalence clause of [Stacks, Tag 0AVW]. -/
def derivedQuasicoherentPushforwardAtModel :
    (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherent X.ringCatSheaf)).FullSubcategory ⥤
      (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherent S.ringCatSheaf)).FullSubcategory :=
  ObjectProperty.lift _
    (ObjectProperty.ι (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherent X.ringCatSheaf)) ⋙
      AlgebraicGeometry.AnyModel.derivedPushforward f)
    (fun E i =>
      AlgebraicGeometry.AnyModel.isQuasicoherent_homologyFunctor_derivedPushforward_of_isAffineHom
        f E.obj E.property i)

/-- **The factorisation asserted by [Stacks, Tag 0AVW], on the quasi-coherent subcategories**:
`Rf_*` is `Φ` followed by the functor `D_QCoh(f_* 𝒪_X) ⥤ D_QCoh(𝒪_S)` of restriction of scalars.
It is `derivedPushforwardOverRingCompRestrictScalarsIso` read on the subcategories, where the
inclusion is fully faithful, so neither the components nor the naturality need any new input. -/
def derivedQuasicoherentPushforwardOverRingCompScalarRestrictionIso :
    derivedQuasicoherentPushforwardOverRing f ⋙ derivedQuasicoherentScalarRestriction.{w} f ≅
      derivedQuasicoherentPushforwardAtModel.{w} f :=
  NatIso.ofComponents
    (fun E => ObjectProperty.isoMk _
      ((derivedPushforwardOverRingCompRestrictScalarsIso.{w} f).app E.obj).symm)
    (fun φ => ObjectProperty.hom_ext _
      ((derivedPushforwardOverRingCompRestrictScalarsIso.{w} f).inv.naturality
        ((ObjectProperty.ι _).map φ)))

end Derived

/-! ### The unit, the counit and the equivalence, at the standard model -/

section Standard

attribute [local instance 10000] HasDerivedCategory.standard

variable [IsAffineHom f]

/-- **`Φ` preserves boundedness below.**  `D^{≥n}` is the right orthogonal of `D^{≤n-1}`, and a
map from an object `L` of `D^{≤n-1}` into `ΦK` is adjoint to a map `Lg^*L ⟶ K` with `Lg^*L` again
in `D^{≤n-1}`, hence zero. -/
theorem isGE_derivedPushforwardOverRing_obj
    (K : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf)) (n : ℤ) (hK : K.IsGE n) :
    ((derivedPushforwardOverRing f).obj K).IsGE n := by
  have := hK
  show DerivedCategory.TStructure.t.IsGE ((derivedPushforwardOverRing f).obj K) n
  rw [DerivedCategory.TStructure.t.isGE_iff_orthogonal (n - 1) n (by omega)]
  intro L g hL
  have := isLE_derivedPullbackOverRing_obj f L (n - 1) hL
  have : (derivedPullbackOverRing f).PreservesZeroMorphisms :=
    inferInstanceAs ((derivedPullback (toPushforwardStructureSpace f)).PreservesZeroMorphisms)
  have hzero := DerivedCategory.TStructure.t.zero
    (((derivedPullbackPushforwardAdjunctionOverRing f).homEquiv L K).symm g) (n - 1) n
    (by omega)
  have hz0 : ((derivedPullbackPushforwardAdjunctionOverRing f).homEquiv L K).symm 0 = 0 := by
    rw [Adjunction.homEquiv_counit, Functor.map_zero, zero_comp]
  exact ((derivedPullbackPushforwardAdjunctionOverRing f).homEquiv L K).symm.injective
    (hzero.trans hz0.symm)

/-- **The counit `Lg^*ΦK ⟶ K` is invertible at a bounded below `K` with quasi-coherent
cohomology.**  Both `𝟭` and `Lg^* ⋙ Φ` are exact, commute with the shift and preserve `D^{≥n}`,
and the counit is invertible on each cohomology object of `K` placed in degree zero, so
`CategoryTheory.NatTrans.isIso_app_of_isGE` applies. -/
theorem isIso_derivedCounitOverRing_app_of_isPlus
    (K : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf))
    (hplus : DerivedCategory.TStructure.t.plus K)
    (hcoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} X.ringCatSheaf) i).obj K).IsQuasicoherent) :
    IsIso ((derivedPullbackPushforwardAdjunctionOverRing f).counit.app K) := by
  let : (derivedPullbackOverRing f).CommShift ℤ :=
    inferInstanceAs ((derivedPullback (toPushforwardStructureSpace f)).CommShift ℤ)
  let : (derivedPullbackOverRing f).IsTriangulated :=
    inferInstanceAs ((derivedPullback (toPushforwardStructureSpace f)).IsTriangulated)
  let : (derivedPushforwardOverRing f).CommShift ℤ :=
    (derivedPullbackPushforwardAdjunctionOverRing f).rightAdjointCommShift ℤ
  let : (derivedPullbackPushforwardAdjunctionOverRing f).CommShift ℤ :=
    (derivedPullbackPushforwardAdjunctionOverRing f).commShift_of_leftAdjoint ℤ
  let : (derivedPullbackPushforwardAdjunctionOverRing f).IsTriangulated :=
    Adjunction.IsTriangulated.mk' (derivedPullbackPushforwardAdjunctionOverRing f)
  obtain ⟨a, hGE⟩ := hplus
  exact NatTrans.isIso_app_of_isGE
    (derivedPullbackPushforwardAdjunctionOverRing f).counit
    (fun L m h => isGE_derivedPullbackOverRing_obj f _ m
      (isGE_derivedPushforwardOverRing_obj f L m h)) (fun _ _ h => h) K a hGE
    (fun q => isIso_derivedCounitOverRing_app_singleFunctor_of_isQuasicoherent f _ (hcoh q))

/-- **`H^j ∘ Rf_*` is `H^j ∘ Φ` followed by restriction of scalars**, naturally: `Rf_*` is `Φ`
followed by the derived restriction of scalars, which commutes with cohomology, being exact. -/
def derivedPushforwardOverRingCompHomologyFunctorIso (j : ℤ) :
    AlgebraicGeometry.AnyModel.derivedPushforward f ⋙
        DerivedCategory.homologyFunctor (SheafOfModules.{u} S.ringCatSheaf) j ≅
      derivedPushforwardOverRing f ⋙ (DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf)) j ⋙ scalarRestriction f) :=
  Functor.isoWhiskerRight (derivedPushforwardOverRingCompRestrictScalarsIso f)
      (DerivedCategory.homologyFunctor (SheafOfModules.{u} S.ringCatSheaf) j) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (derivedPushforwardOverRing f)
      ((scalarRestriction f).mapDerivedCategoryCompHomologyFunctorIso j)

omit [IsAffineHom f] in
/-- **`H^j(Φα)` is invertible as soon as `H^j(Rf_*α)` is.**  The two are the same map up to
restriction of scalars along `𝒪_S ⟶ f_* 𝒪_X`, which reflects isomorphisms. -/
theorem isIso_homologyFunctor_map_derivedPushforwardOverRing_map (j : ℤ)
    {E F' : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf)} (α : E ⟶ F')
    (h : IsIso ((DerivedCategory.homologyFunctor (SheafOfModules.{u} S.ringCatSheaf) j).map
      ((AlgebraicGeometry.AnyModel.derivedPushforward f).map α))) :
    IsIso ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf)) j).map
      ((derivedPushforwardOverRing f).map α)) := by
  have h2 := (NatIso.isIso_map_iff (derivedPushforwardOverRingCompHomologyFunctorIso f j) α).1 h
  have h3 : IsIso ((scalarRestriction f).map ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf)) j).map
      ((derivedPushforwardOverRing f).map α))) := h2
  exact isIso_of_reflects_iso _ (scalarRestriction f)

/-- **The counit `Lg^*ΦK ⟶ K` is invertible for every `K` of `D_QCoh(𝒪_X)`** — this is the
essential content of [Stacks, Tag 0AVW].

Fix a degree `j` and truncate at `-n ≤ j`.  The truncation map `K ⟶ τ_{≥ -n}K` is invertible on
`H^j`; the counit at `τ_{≥ -n}K` is invertible because that object is bounded below with
quasi-coherent cohomology; and `Φ` of the truncation map is invertible on `H^j`, because `Rf_*` of
it is, by part (2) of [Stacks, Tag 08D4] for an affine morphism.  Applying
`H^j ∘ Lg^* = g^* ∘ H^j` and reading the naturality square of the counit identifies `H^j` of the
counit at `K` with an isomorphism. -/
theorem isIso_derivedCounitOverRing_app_of_isQuasicoherent
    (K : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf))
    (hcoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} X.ringCatSheaf) i).obj K).IsQuasicoherent) :
    IsIso ((derivedPullbackPushforwardAdjunctionOverRing f).counit.app K) := by
  rw [DerivedCategory.isIso_iff]
  intro j
  obtain ⟨n, hn⟩ : ∃ n : ℕ, -(n : ℤ) ≤ j := ⟨(-j).toNat, by omega⟩
  have hP := containsZero_isQuasicoherent X
  have hcohtr : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} X.ringCatSheaf) i).obj
      ((DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).obj K)).IsQuasicoherent := fun i =>
    @Stacks.SmallDerivedCategory.prop_homologyFunctor_truncGE_obj _ _ _ _
      (SheafOfModules.isQuasicoherent X.ringCatSheaf) _ hP K hcoh (-(n : ℤ)) i
  have hε := isIso_derivedCounitOverRing_app_of_isPlus f
    ((DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).obj K) ⟨-(n : ℤ), inferInstance⟩ hcohtr
  have hπ := DerivedCategory.isIso_homologyMap_truncGEπ_app (C :=
    SheafOfModules.{u} X.ringCatSheaf) (-(n : ℤ)) j hn K
  have hRπ : IsIso ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf)) j).map
      ((derivedPushforwardOverRing f).map
        ((DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app K))) :=
    isIso_homologyFunctor_map_derivedPushforwardOverRing_map f j _
      (AlgebraicGeometry.isIso_homologyFunctor_map_derivedPushforward_truncGEπ f K hcoh
        (-(n : ℤ)) j hn)
  have hLRπ : IsIso ((DerivedCategory.homologyFunctor (SheafOfModules.{u} X.ringCatSheaf) j).map
      ((derivedPullbackOverRing f).map ((derivedPushforwardOverRing f).map
        ((DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app K)))) := by
    refine (isIso_homologyFunctor_map_derivedPullbackOverRing_map_iff f j _).2 ?_
    have := hRπ
    infer_instance
  have hnat : (DerivedCategory.homologyFunctor (SheafOfModules.{u} X.ringCatSheaf) j).map
        ((derivedPullbackOverRing f).map ((derivedPushforwardOverRing f).map
          ((DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app K))) ≫
        (DerivedCategory.homologyFunctor (SheafOfModules.{u} X.ringCatSheaf) j).map
          ((derivedPullbackPushforwardAdjunctionOverRing f).counit.app
            ((DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).obj K)) =
      (DerivedCategory.homologyFunctor (SheafOfModules.{u} X.ringCatSheaf) j).map
          ((derivedPullbackPushforwardAdjunctionOverRing f).counit.app K) ≫
        (DerivedCategory.homologyFunctor (SheafOfModules.{u} X.ringCatSheaf) j).map
          ((DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app K) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (DerivedCategory.homologyFunctor (SheafOfModules.{u} X.ringCatSheaf) j).map
      ((derivedPullbackPushforwardAdjunctionOverRing f).counit.naturality
        ((DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app K))
  have hcomp : IsIso ((DerivedCategory.homologyFunctor (SheafOfModules.{u} X.ringCatSheaf) j).map
      ((derivedPullbackPushforwardAdjunctionOverRing f).counit.app K) ≫
      (DerivedCategory.homologyFunctor (SheafOfModules.{u} X.ringCatSheaf) j).map
        ((DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app K)) := by
    rw [← hnat]
    exact IsIso.comp_isIso' hLRπ
      ((DerivedCategory.homologyFunctor (SheafOfModules.{u} X.ringCatSheaf) j).mapIso
        (@asIso _ _ _ _ _ hε)).isIso_hom
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ hπ hcomp

/-- **The unit `M ⟶ ΦLg^*M` is invertible for every `M` of `D_QCoh(f_* 𝒪_X)`.**  By the triangle
identity, `Lg^*` of the unit at `M` composed with the counit at `Lg^*M` is the identity, and the
latter is invertible because `Lg^*M` lies in `D_QCoh(𝒪_X)`; so `Lg^*` of the unit is invertible.
Degreewise this says that `g^*H^j` of the unit is invertible, and `g^*` reflects isomorphisms
between quasi-coherent modules, which `H^j(M)` and `H^j(ΦLg^*M)` both are. -/
theorem isIso_derivedUnitOverRing_app_of_isQuasicoherent
    (M : DerivedCategory (SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf)))
    (hcoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf)) i).obj M).IsQuasicoherent) :
    IsIso ((derivedPullbackPushforwardAdjunctionOverRing f).unit.app M) := by
  have hLM := isQuasicoherent_homologyFunctor_derivedPullbackOverRing_of_isAffineHom f M hcoh
  have hε := isIso_derivedCounitOverRing_app_of_isQuasicoherent f
    ((derivedPullbackOverRing f).obj M) hLM
  have hLη : IsIso ((derivedPullbackOverRing f).map
      ((derivedPullbackPushforwardAdjunctionOverRing f).unit.app M)) := by
    have htri : IsIso ((derivedPullbackOverRing f).map
        ((derivedPullbackPushforwardAdjunctionOverRing f).unit.app M) ≫
        (derivedPullbackPushforwardAdjunctionOverRing f).counit.app
          ((derivedPullbackOverRing f).obj M)) := by
      rw [(derivedPullbackPushforwardAdjunctionOverRing f).left_triangle_components M]
      exact (Iso.refl _).isIso_hom
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ hε htri
  rw [DerivedCategory.isIso_iff]
  intro j
  refine isIso_of_isIso_pullbackModules_map f (hcoh j)
    (isQuasicoherent_homologyFunctor_derivedPushforwardOverRing_of_isAffineHom f
      ((derivedPullbackOverRing f).obj M) hLM j) _ ?_
  refine (isIso_homologyFunctor_map_derivedPullbackOverRing_map_iff f j _).1 ?_
  have := hLη
  infer_instance

/-- **`Φ : D_QCoh(𝒪_X) ⥤ D_QCoh(f_* 𝒪_X)` is an equivalence**, for `f` an affine morphism of
schemes.  This is the first clause of [Stacks, Tag 0AVW].

`Φ` is fully faithful because `D_QCoh(𝒪_X)` is contained in the subcategory of [Stacks, Tag 0D7R]
where the counit is invertible, and essentially surjective because the unit exhibits every `M` of
`D_QCoh(f_* 𝒪_X)` as `Φ(Lg^*M)` with `Lg^*M` again in `D_QCoh(𝒪_X)`. -/
theorem isEquivalence_derivedQuasicoherentPushforwardOverRing :
    (derivedQuasicoherentPushforwardOverRing f).IsEquivalence := by
  have hCounitB : DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherent X.ringCatSheaf) ≤
      (derivedPullbackPushforwardAdjunctionOverRing f).counitIsIso := fun K hK =>
    isIso_derivedCounitOverRing_app_of_isQuasicoherent f K hK
  let hR : ((DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι ⋙
        derivedPushforwardOverRing f).FullyFaithful :=
    ((ObjectProperty.fullyFaithfulιOfLE hCounitB).comp
      (derivedPullbackPushforwardAdjunctionOverRing f).fullyFaithfulιCompRightAdjoint).ofIso
        ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight
          (ObjectProperty.ιOfLECompιIso hCounitB) (derivedPushforwardOverRing f))
  let := hR.full
  let := hR.faithful
  let hiso : derivedQuasicoherentPushforwardOverRing f ⋙
      (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent
        (pushforwardRing f.base X.ringCatSheaf))).ι ≅
      (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι ⋙
        derivedPushforwardOverRing f := Iso.refl _
  let : (derivedQuasicoherentPushforwardOverRing f).Faithful :=
    Functor.Faithful.of_comp_iso hiso
  let : (derivedQuasicoherentPushforwardOverRing f).Full :=
    Functor.Full.of_comp_faithful_iso hiso
  let : (derivedQuasicoherentPushforwardOverRing f).EssSurj :=
    ⟨fun M => ⟨⟨(derivedPullbackOverRing f).obj M.obj, fun i =>
      isQuasicoherent_homologyFunctor_derivedPullbackOverRing_of_isAffineHom f
        M.obj M.property i⟩,
      ⟨ObjectProperty.isoMk _ (@asIso _ _ _ _ _
        (isIso_derivedUnitOverRing_app_of_isQuasicoherent f M.obj M.property)).symm⟩⟩⟩
  exact { }

/-- **[Stacks, Tag 0AVW], the whole statement.**  Let `f : X ⟶ S` be an affine morphism of
schemes.  Then direct image induces an **equivalence**
`Φ : D_QCoh(𝒪_X) ⥤ D_QCoh(f_* 𝒪_X)`, and the composition of `Φ` with the functor
`D_QCoh(f_* 𝒪_X) ⥤ D_QCoh(𝒪_S)` given by restriction of scalars along `𝒪_S ⟶ f_* 𝒪_X` **is**
`Rf_*`.

Both clauses are read on the quasi-coherent subcategories and under the source's condition that
`f` be affine, which is where the tag's own statement puts them; the existing registration on
`derivedPushforwardOverRingCompRestrictScalarsIso` carries the second clause alone, for every
morphism of schemes and on the whole derived categories. -/
@[stacks 0AVW]
theorem isEquivalence_and_factorisation_derivedQuasicoherentPushforwardOverRing :
    (derivedQuasicoherentPushforwardOverRing f).IsEquivalence ∧
      Nonempty (derivedQuasicoherentPushforwardOverRing f ⋙
          derivedQuasicoherentScalarRestriction f ≅
        derivedQuasicoherentPushforwardAtModel f) :=
  ⟨isEquivalence_derivedQuasicoherentPushforwardOverRing f,
    ⟨derivedQuasicoherentPushforwardOverRingCompScalarRestrictionIso f⟩⟩

end Standard

end Stacks.AlgebraicGeometry.DerivedAffinePushforward

end
