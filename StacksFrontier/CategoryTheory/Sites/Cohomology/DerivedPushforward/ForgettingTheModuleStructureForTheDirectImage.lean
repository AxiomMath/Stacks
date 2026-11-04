module

public import Mathlib.Algebra.Homology.Functor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.LerayForUnboundedSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.ForgettingTheModuleStructure
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.UnderlyingAbelianLocalCohomologyInvertible
import StacksCore.Tactic.StacksAttribute

/-!
# Forgetting the module structure in the unbounded derived direct image

Let `f : (C, O_C) ⟶ (D, O_D)` be a morphism of ringed sites, given by a continuous functor
`u : D ⥤ C` which is a morphism of sites, and let `K` be an object of `D(O_C)`. Writing `K_ab`
for the image of `K` in the unbounded derived category of abelian sheaves, there is a canonical
map

`Rf_*K ⟶ Rf_*(K_ab)`

and it is an isomorphism in `D(Z_D)`. This is the third assertion of Stacks 0D6J; the first two,
about derived global sections and about derived sections over an object of the site, are
`Stacks.Cohomology.ForgetModule.globalSectionsForgetComparison_isIso` and
`Stacks.Cohomology.ForgetModule.sectionsForgetComparison_isIso`.

The map is the one the source constructs: it is induced, through the universal property of the
right derived functor of degreewise direct image, by the identity identification
`f_*(M_ab) = (f_*M)_ab` of the two underived composites. No flatness and no other hypothesis on
`f` is assumed, and `K` is unbounded.

## Main definitions

* `Stacks.Cohomology.ForgetModule.abelianPushforward`,
  `Stacks.Cohomology.ForgetModule.derivedAbelianPushforward`: degreewise direct image of abelian
  sheaves along `u`, and its unbounded right derived functor `Rf_*` on `D(Z_C)`.
* `Stacks.Cohomology.ForgetModule.pushforwardForgetComparison`: the canonical map
  `Rf_*K ⟶ Rf_*(K_ab)`.

## Main results

* `Stacks.Cohomology.ForgetModule.pushforwardForgetComparison_isIso` (Tag 0D6J, part (3)): that
  map is an isomorphism, naturally in `K`.
* `Stacks.Cohomology.ForgetModule.quasiIso_abelianPushforward_map_of_isKInjective`: degreewise
  direct image of abelian sheaves carries a K-injective resolution of the underlying abelian
  complex of a K-injective complex of `O_C`-modules to a quasi-isomorphism.
* `Stacks.Cohomology.ForgetModule.rightDerivedUnit_isIso_of_quasiIso_degreewise`: a right
  derived unit is invertible at a complex whose chosen K-injective resolution the degreewise
  functor already turns into a quasi-isomorphism.

## Implementation notes

The source's own proof is followed, and the unbounded case is what forces the shape of the
argument. Right derived functors over a Grothendieck abelian category are absolute
(`Stacks.Cohomology.UnboundedComplexes.isRightDerivedFunctor_comp`), so `Rf_*` followed by the
forgetful functor on derived categories is again a right derived functor of degreewise direct
image followed by forgetting; the whole content is therefore that *the other* composite,
forgetting first and then deriving the abelian direct image, is a right derived functor of the
same functor on `K(Mod(O_C))`. By `Stacks.Cohomology.Localization.rightDerived_of_kInjectives`
that is the single statement

> for `I` a K-injective complex of `O_C`-modules, the unit of the abelian `Rf_*` is invertible
> at the underlying abelian complex `I_ab`,

which is false for the trivial reason that `I_ab` is K-injective — it is not — and true for the
reason of Stacks 0D6J: `I_ab` still computes derived sections. Concretely, let `I_ab ⟶ J` be a
K-injective resolution of abelian sheaves. Its direct image is a quasi-isomorphism because
quasi-isomorphy of a morphism of complexes of sheaves is detected on the underlying complexes of
presheaves, hence object by object of `D`
(`Stacks.Cohomology.SupportedComplexes.sheafQuasiIso_of_presheafQuasiIso` together with
`HomologicalComplex.quasiIso_iff_evaluation`), and sections over `V` of a direct image are
sections over `u(V)` on the nose. Sections over an object are corepresented by the free abelian
sheaf on that object, which is sectionwise torsion free, so
`Stacks.Cohomology.DerivedLowerShriek.quasiIso_mapHomologicalComplex_of_corepresentable` applies;
its hypothesis is exactly
`Stacks.Cohomology.ForgetModule.qh_map_bijective_single_of_isKInjective`, the half of the
argument of parts (1) and (2) which says that morphisms out of a bounded-above sectionwise
torsion-free complex into `I_ab` are already computed in the homotopy category.

So nothing beyond parts (1) and (2) is needed, and in particular the comparison of the cohomology
sheaves of `Rf_*` with the sheafified cohomology presheaves — which the module docstring of
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedSections/ForgettingTheModuleStructure.lean`
named as the missing input, and which the library has for sheaves of modules only — is not used.

Unlike `Stacks.Cohomology.LerayUnbounded.derivedSectionsOverObjectPushforwardIsoOfFlat`, nothing
here needs Stacks 093Y: degreewise direct image is *not* asked to preserve K-injectivity. The
absoluteness of right derived functors replaces it, because the functor applied after `Rf_*` —
forgetting the module structure — is applied on the derived category and not degreewise.

The three universes of the ringed sites are collapsed, as they are in
`AlgebraicGeometry.RingedSite.Hom` and throughout the derived development, and no hypothesis of
the form "`u` is a morphism of ringed topoi" is carried: `AlgebraicGeometry.RingedSite.Hom`
stores `isMorphismOfSites`.

## References

* [Stacks Project, Tag 0D6J](https://stacks.math.columbia.edu/tag/0D6J)
* [Stacks Project, Tag 07A5](https://stacks.math.columbia.edu/tag/07A5)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open ModuleSheafCohomology
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

universe u

namespace Stacks.Cohomology.ForgetModule

universe v v₁ v₂ u₁ u₂ w

section General

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [IsGrothendieckAbelian.{w} A]
  [HasDerivedCategory.{v} A] {B : Type u₂} [Category.{v₂} B] [Abelian B]
  [HasDerivedCategory.{v} B]

/-- **A right-derived unit is invertible at a complex admitting a K-injective resolution that
the degreewise functor turns into a quasi-isomorphism.** This is
`Stacks.Cohomology.DerivedLowerShriek.rightDerivedUnit_isIso_of_quasiIso_resolution` for a
functor of the shape "apply `G` degreewise, then localize", with its hypothesis translated into
a statement about complexes. The resolution is arbitrary — which matters when the complex at
hand comes with a resolution of its own, as the inverse image of one does. -/
theorem rightDerivedUnit_isIso_of_quasiIso_resolution_degreewise (G : A ⥤ B) [G.Additive]
    (RG : DerivedCategory A ⥤ DerivedCategory B)
    (α : G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RG)
    [RG.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    {M N : CochainComplex A ℤ} (q : M ⟶ N) [QuasiIso q] [N.IsKInjective]
    (hq : QuasiIso ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map q)) :
    IsIso (α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj M)) := by
  have := hq
  refine DerivedLowerShriek.rightDerivedUnit_isIso_of_quasiIso_resolution _ RG α q ?_
  change IsIso (DerivedCategory.Qh.map ((G.mapHomotopyCategory (ComplexShape.up ℤ)).map
    ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map q)))
  rw [Functor.mapHomotopyCategory_map]
  exact _root_.isIso_Qh_map_quotient_map_of_quasiIso _

/-- **A right-derived unit is invertible at a complex whose chosen K-injective resolution the
degreewise functor already turns into a quasi-isomorphism.** -/
theorem rightDerivedUnit_isIso_of_quasiIso_degreewise (G : A ⥤ B) [G.Additive]
    (RG : DerivedCategory A ⥤ DerivedCategory B)
    (α : G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RG)
    [RG.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (M : CochainComplex A ℤ)
    (hM : QuasiIso ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map
      ((Stacks.Injectives.kInjectiveResolutionInclusion A).app M))) :
    IsIso (α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj M)) :=
  rightDerivedUnit_isIso_of_quasiIso_resolution_degreewise G RG α
    ((Stacks.Injectives.kInjectiveResolutionInclusion A).app M) hM

end General

section AbelianDirectImage

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [Category.{u} C] {D : Type u} [Category.{u} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (w : D ⥤ C) [w.IsContinuous K J]

/-- Degreewise direct image of abelian sheaves along a continuous functor of sites:
precomposition of the underlying presheaf with `w`. -/
abbrev abelianPushforward : Sheaf J AddCommGrpCat.{u} ⥤ Sheaf K AddCommGrpCat.{u} :=
  w.sheafPushforwardContinuous AddCommGrpCat.{u} K J

/-- Degreewise direct image of complexes of abelian sheaves, followed by localization. -/
abbrev homotopyAbelianPushforward :
    HomotopyCategory (Sheaf J AddCommGrpCat.{u}) (ComplexShape.up ℤ) ⥤
      DerivedCategory (Sheaf K AddCommGrpCat.{u}) :=
  (abelianPushforward J K w).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh

/-- **Stacks 07A5 for the direct image of abelian sheaves:** degreewise direct image followed by
localization has a right derived functor on the whole unbounded derived category, abelian
sheaves on a small site being Grothendieck abelian. -/
@[sga "4 XVII 5.4.1" "partial"]
instance abelianPushforward_hasRightDerivedFunctor :
    (homotopyAbelianPushforward J K w).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (Sheaf J AddCommGrpCat.{u}) (ComplexShape.up ℤ)) :=
  DerivedLowerShriek.alongFunctor_hasRightDerivedFunctor_of_isGrothendieckAbelian _

/-- The unbounded total direct image `Rf_*` of abelian sheaves. -/
abbrev derivedAbelianPushforward :
    DerivedCategory (Sheaf J AddCommGrpCat.{u}) ⥤
      DerivedCategory (Sheaf K AddCommGrpCat.{u}) :=
  (homotopyAbelianPushforward J K w).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso (Sheaf J AddCommGrpCat.{u}) (ComplexShape.up ℤ))

/-- The canonical comparison from degreewise to derived direct image of abelian sheaves. -/
abbrev derivedAbelianPushforwardUnit :
    homotopyAbelianPushforward J K w ⟶
      DerivedCategory.Qh ⋙ derivedAbelianPushforward J K w :=
  (homotopyAbelianPushforward J K w).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso (Sheaf J AddCommGrpCat.{u}) (ComplexShape.up ℤ))

variable (O : Sheaf J RingCat.{u})

/-- **Degreewise direct image takes a K-injective resolution of the underlying abelian complex
of a K-injective complex of modules to a quasi-isomorphism.** Quasi-isomorphy of a morphism of
complexes of abelian sheaves is detected on the underlying complexes of presheaves, hence object
by object of the target site; sections over `V` of a direct image are sections over `w(V)` on the
nose; and those are corepresented by the free abelian sheaf on `w(V)`, which is sectionwise
torsion free, so the corepresentable criterion applies with the bijectivity statement of parts
(1) and (2) of Tag 0D6J as its input. -/
theorem quasiIso_abelianPushforward_map_of_isKInjective
    (I : CochainComplex (SheafOfModules.{u} O) ℤ) [I.IsKInjective]
    {Jc : CochainComplex (Sheaf J AddCommGrpCat.{u}) ℤ} [Jc.IsKInjective]
    (q : ((SheafOfModules.toSheaf O).mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ Jc)
    [QuasiIso q] :
    QuasiIso (((abelianPushforward J K w).mapHomologicalComplex (ComplexShape.up ℤ)).map q) := by
  apply SupportedComplexes.sheafQuasiIso_of_presheafQuasiIso K
  rw [HomologicalComplex.quasiIso_iff_evaluation]
  intro t
  change QuasiIso ((((sheafSections J AddCommGrpCat.{u}).obj
    (op (w.obj t.unop))).mapHomologicalComplex (ComplexShape.up ℤ)).map q)
  refine DerivedLowerShriek.quasiIso_mapHomologicalComplex_of_corepresentable
    _ _ (evaluationRepresentation J (w.obj t.unop)).symm q (fun n => ?_)
  have : QuasiIso (q⟦n⟧') := by
    change QuasiIso ((CategoryTheory.shiftFunctor
      (CochainComplex (Sheaf J AddCommGrpCat.{u}) ℤ) n).map q)
    infer_instance
  have := _root_.isIso_Qh_map_quotient_map_of_quasiIso (q⟦n⟧')
  refine DerivedLowerShriek.bijective_postcomp_of_qh_bijective _
    (qh_map_bijective_single_of_isKInjective J O _
      (fun V => isTorsionFree_sheafify J _ (fun W => by
        change Module.IsTorsionFree ℤ (FreeAbelianGroup (W.unop ⟶ w.obj t.unop))
        exact Module.Flat.isTorsionFree) V) I n)
    (CochainComplex.IsKInjective.Qh_map_bijective _ (Jc⟦n⟧))

/-- **The underlying abelian complex of a K-injective complex of modules computes the derived
direct image of abelian sheaves**, in the sense that the comparison from degreewise to derived
direct image is invertible there. -/
theorem abelianPushforwardUnit_isIso_at_underlying_kInjective
    (I : CochainComplex (SheafOfModules.{u} O) ℤ) [I.IsKInjective] :
    IsIso ((derivedAbelianPushforwardUnit J K w).app
      ((HomotopyCategory.quotient (Sheaf J AddCommGrpCat.{u}) (ComplexShape.up ℤ)).obj
        (((SheafOfModules.toSheaf O).mapHomologicalComplex (ComplexShape.up ℤ)).obj I))) :=
  rightDerivedUnit_isIso_of_quasiIso_degreewise (abelianPushforward J K w)
    (derivedAbelianPushforward J K w) (derivedAbelianPushforwardUnit J K w) _
    (quasiIso_abelianPushforward_map_of_isKInjective J K w O I _)

end AbelianDirectImage

section Pushforward

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat
attribute [local instance] AlgebraicGeometry.RingedSite.Hom.pushforwardTopos_additive

variable {X Y : RingedSite.{u, u, u}} (f : RingedSite.Hom X Y)

/-- The canonical unit comparison for the unbounded derived direct image after forgetting the
module structure, assembled from the identity identification `f_*(M_ab) = (f_*M)_ab` of the
underived composites and the comparison for the abelian derived direct image. -/
def pushforwardForgetUnit :
    @Quiver.Hom
      (HomotopyCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (ComplexShape.up ℤ) ⥤
        DerivedCategory (Sheaf Y.J AddCommGrpCat.{u})) _
      (pushforwardOnHomotopy.{u} f.toRingedToposSiteHom ⋙ underlyingDerivedSheaf Y)
      (DerivedCategory.Qh (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⋙
        (underlyingDerivedSheaf X ⋙ derivedAbelianPushforward X.J Y.J f.u)) :=
  letI : @Functor.Additive (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (Sheaf Y.J AddCommGrpCat.{u}) SheafOfModules.instCategory _ _ _
      (SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) := ⟨rfl⟩
  letI : @Functor.Additive (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (Sheaf Y.J AddCommGrpCat.{u}) SheafOfModules.instCategory _ _ _
      (SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
        abelianPushforward X.J Y.J f.u) := ⟨rfl⟩
  Functor.whiskerLeft
      (f.toRingedToposSiteHom.pushforwardTopos.mapHomotopyCategory (ComplexShape.up ℤ))
      (SheafOfModules.toSheaf
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).mapDerivedCategoryFactorsh.hom ≫
    Functor.whiskerRight
      (Functor.mapHomotopyCategoryCompIso
        (show f.toRingedToposSiteHom.pushforwardTopos ⋙
              SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ≅
            SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
              abelianPushforward X.J Y.J f.u from Iso.refl _)
        (ComplexShape.up ℤ)).hom DerivedCategory.Qh ≫
    Functor.whiskerRight
      (Functor.mapHomotopyCategoryCompIso
        (Iso.refl (SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
          abelianPushforward X.J Y.J f.u))
        (ComplexShape.up ℤ)).inv DerivedCategory.Qh ≫
    Functor.whiskerLeft
      ((SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomotopyCategory
        (ComplexShape.up ℤ))
      (derivedAbelianPushforwardUnit X.J Y.J f.u) ≫
    Functor.whiskerRight
      (SheafOfModules.toSheaf
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapDerivedCategoryFactorsh.inv
      (derivedAbelianPushforward X.J Y.J f.u)

/-- The comparison exhibiting `Rf_*` followed by forgetting the module structure as a right
derived functor of degreewise direct image followed by forgetting. This is the absoluteness of
right derived functors over a Grothendieck abelian category. -/
abbrev pushforwardForgetBeta :
    pushforwardOnHomotopy.{u} f.toRingedToposSiteHom ⋙ underlyingDerivedSheaf Y ⟶
      DerivedCategory.Qh ⋙ (derivedPushforward.{u} f.toRingedToposSiteHom ⋙
        underlyingDerivedSheaf Y) :=
  Functor.whiskerRight (derivedPushforwardUnit.{u} f.toRingedToposSiteHom)
      (underlyingDerivedSheaf Y) ≫
    (Functor.associator DerivedCategory.Qh (derivedPushforward.{u} f.toRingedToposSiteHom)
      (underlyingDerivedSheaf Y)).hom

/-- The derived direct image followed by forgetting the module structure is a right derived
functor of degreewise direct image followed by forgetting, along `pushforwardForgetBeta`. -/
instance isRightDerivedFunctor_pushforwardForgetBeta :
    (derivedPushforward.{u} f.toRingedToposSiteHom ⋙
        underlyingDerivedSheaf Y).IsRightDerivedFunctor (pushforwardForgetBeta f)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ)) :=
  UnboundedComplexes.isRightDerivedFunctor_comp _ _ _ _ _

/-- **The canonical map `Rf_*K ⟶ Rf_*(K_ab)`**, induced by `pushforwardForgetUnit` through the
universal property of the right derived functor of degreewise direct image. -/
def pushforwardForgetComparison :
    derivedPushforward.{u} f.toRingedToposSiteHom ⋙ underlyingDerivedSheaf Y ⟶
      underlyingDerivedSheaf X ⋙ derivedAbelianPushforward X.J Y.J f.u :=
  (derivedPushforward.{u} f.toRingedToposSiteHom ⋙
      underlyingDerivedSheaf Y).rightDerivedDesc
    (pushforwardForgetBeta f)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ))
    _ (pushforwardForgetUnit f)

/-- The unit comparison is invertible at a complex of `O_C`-modules whose underlying abelian
complex computes the derived direct image of abelian sheaves: all but one of its factors are
isomorphisms, and the remaining one is that hypothesis. -/
theorem pushforwardForgetUnit_isIso_app_of_abelianUnit
    (I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hα : IsIso ((derivedAbelianPushforwardUnit X.J Y.J f.u).app
      ((HomotopyCategory.quotient (Sheaf X.J AddCommGrpCat.{u}) (ComplexShape.up ℤ)).obj
        (((SheafOfModules.toSheaf
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I)))) :
    IsIso ((pushforwardForgetUnit f).app
      ((HomotopyCategory.quotient (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ)).obj I)) := by
  have hα' : IsIso ((derivedAbelianPushforwardUnit X.J Y.J f.u).app
      (((SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomotopyCategory
        (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (ComplexShape.up ℤ)).obj I))) :=
    (NatTrans.isIso_app_iff_of_iso (derivedAbelianPushforwardUnit X.J Y.J f.u)
      (((SheafOfModules.toSheaf
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomotopyCategoryFactors
        (ComplexShape.up ℤ)).app I)).mp hα
  dsimp only [pushforwardForgetUnit]
  refine IsIso.comp_isIso' ?_ (IsIso.comp_isIso' ?_ (IsIso.comp_isIso' ?_
    (IsIso.comp_isIso' ?_ ?_)))
  · exact Iso.isIso_hom ((Functor.isoWhiskerLeft _ _).app _)
  · exact Iso.isIso_hom ((Functor.isoWhiskerRight _ _).app _)
  · exact Iso.isIso_inv ((Functor.isoWhiskerRight _ _).app _)
  · exact hα'
  · exact Iso.isIso_inv ((Functor.isoWhiskerRight _ _).app _)

/-- The unit comparison is invertible at a K-injective complex of `O_C`-modules: the hypothesis
of `pushforwardForgetUnit_isIso_app_of_abelianUnit` is then
`abelianPushforwardUnit_isIso_at_underlying_kInjective`. -/
theorem pushforwardForgetUnit_isIso_app_of_isKInjective
    (I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [I.IsKInjective] :
    IsIso ((pushforwardForgetUnit f).app
      ((HomotopyCategory.quotient (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ)).obj I)) :=
  pushforwardForgetUnit_isIso_app_of_abelianUnit f I
    (abelianPushforwardUnit_isIso_at_underlying_kInjective X.J Y.J f.u
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) I)

/-- Forgetting the module structure and then deriving the abelian direct image is a right
derived functor of degreewise direct image followed by forgetting, because the unit comparison
is invertible on K-injective complexes of `O_C`-modules. -/
instance pushforwardForgetTarget_isRightDerivedFunctor :
    (underlyingDerivedSheaf X ⋙
        derivedAbelianPushforward X.J Y.J f.u).IsRightDerivedFunctor (pushforwardForgetUnit f)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ)) :=
  Localization.rightDerived_of_kInjectives _ _ _ fun I _ =>
    pushforwardForgetUnit_isIso_app_of_isKInjective f I

/-- **Stacks 0D6J, part (3).** Let `f : (C, O_C) ⟶ (D, O_D)` be a morphism of ringed sites. For
`K` in the unbounded derived category `D(O_C)` the canonical map `Rf_*K ⟶ Rf_*(K_ab)` from the
image in `D(Z_D)` of the unbounded derived direct image of `K` to the unbounded derived direct
image of the underlying abelian complex of `K` is an isomorphism, naturally in `K`. -/
@[stacks 0D6J "part (3): the unbounded derived direct image along a morphism of ringed sites"]
theorem pushforwardForgetComparison_isIso : IsIso (pushforwardForgetComparison f) :=
  (Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc
    (derivedPushforward.{u} f.toRingedToposSiteHom ⋙ underlyingDerivedSheaf Y)
    (pushforwardForgetBeta f)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ))
    (underlyingDerivedSheaf X ⋙ derivedAbelianPushforward X.J Y.J f.u)
    (pushforwardForgetUnit f)).mp (pushforwardForgetTarget_isRightDerivedFunctor f)

end Pushforward

end Stacks.Cohomology.ForgetModule

end
