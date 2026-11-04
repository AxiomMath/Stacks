module

public import StacksFrontier.AlgebraicGeometry.Etale.FiniteSupportComparison
public import StacksFrontier.AlgebraicGeometry.Etale.OpenCovariance
public import StacksFrontier.Algebra.Category.Grp.FilteredColimit

/-!
# Injectivity of covariance for the finite-support direct image

Let `j : X' ⟶ X` be an open immersion and let `f : X ⟶ Y` be locally of finite type and locally
quasi-finite in a big étale site. Extension by zero of a section supported on a support finite
over an étale test object is injective, so for a *separated* `f` the covariance map
`(j ≫ f)_{p!}(F|_{X'}) ⟶ f_{p!}F` of Stacks 0F6S is injective over every test object, and its
sheafification `(j ≫ f)_!(F|_{X'}) ⟶ f_!F` is a monomorphism.

## Main results

* `AlgebraicGeometry.SmallEtale.covarianceSectionMap_injective` — extension by zero is injective
  on sections supported on a support finite over the test object; this needs no separatedness.
* `AlgebraicGeometry.SmallEtale.mono_openCovarianceShriekMap_app_of_mono_app` — the covariance
  map of the direct images with compact support is a monomorphism as soon as the presheaf
  covariance map is one over every test object; this needs no separatedness.
* `AlgebraicGeometry.SmallEtale.covarianceColimitMap_injective` and
  `AlgebraicGeometry.SmallEtale.mono_covariancePresheafMap` — for a separated morphism the
  covariance map of finite-support direct-image presheaves is injective.
* `AlgebraicGeometry.SmallEtale.mono_openCovarianceShriekMap_app` — for a separated morphism the
  covariance map of the direct images with compact support is a monomorphism.

## Implementation notes

Injectivity of extension by zero is the statement that the extended section is determined by its
restriction to the canonical open of the original support, which is exactly what
`AlgebraicGeometry.SmallEtale.covarianceSectionMap_restrict` says, the comparison of the two
descriptions of the restriction of an abelian sheaf to an open subscheme being an isomorphism.

Passing from the generators to the colimit uses that the eligible supports over a test object
form a *filtered* category, which is where separatedness enters: for a separated morphism an
eligible support is closed in the base change, so the union of two eligible supports is again
one. Without separatedness an eligible support is only locally closed and two of them need not be
contained in a third — for the line with a doubled origin over the affine line each of the two
copies of the line is an eligible support while their union, the whole non-separated source, is
not — so the vanishing of a germ in the colimit cannot be tested on a single transition map and
injectivity of the presheaf map is not available by this argument. Stacks 0F6S checks part (4) on
stalks instead, which needs the stalk compatibility of part (1).

Monomorphy of the sheafified map follows from monomorphy of the presheaf map because
sheafification of abelian sheaves is left exact.

## References

* [Stacks Project, Tag 0F6S](https://stacks.math.columbia.edu/tag/0F6S)
* [Stacks Project, Tag 0F6M](https://stacks.math.columbia.edu/tag/0F6M)
* [Stacks Project, Tag 0F6F](https://stacks.math.columbia.edu/tag/0F6F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.SmallEtale

section Generator

variable (B : BigEtaleSite.{u}) {X' X Y : B.Scheme} (j : X' ⟶ X) (f : X ⟶ Y)
  [IsOpenImmersion (B.inclusion.map j)]
  (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})

/-- Extension by zero of a section supported on a support finite over the test object is
injective: the extended section restricts back to the original one. -/
public theorem covarianceSectionMap_injective (V : SmallEtale B Y.obj Y.property)
    (E : FiniteSupport B (j ≫ f) V) (D : FiniteSupport B f V)
    (hD : D.1 = (openBaseChangeHom B j f V).base '' E.1) :
    Function.Injective (covarianceSectionMap B j f F V E D hD) := by
  have hid : ∀ t, ((openRestrictionIso.{u, v} B j).hom.app F).hom.app
        (op (openCovarianceSupportObject B (j ≫ f) V E))
        (((openRestrictionIso.{u, v} B j).inv.app F).hom.app
          (op (openCovarianceSupportObject B (j ≫ f) V E)) t) = t := fun t =>
    ConcreteCategory.congr_hom
      (congrArg (fun k => k.hom.app (op (openCovarianceSupportObject B (j ≫ f) V E)))
        ((openRestrictionIso.{u, v} B j).inv_hom_id_app F)) t
  intro a b h
  apply Subtype.ext
  have hinv : ((openRestrictionIso.{u, v} B j).inv.app F).hom.app
        (op (openCovarianceSupportObject B (j ≫ f) V E)) a.val =
      ((openRestrictionIso.{u, v} B j).inv.app F).hom.app
        (op (openCovarianceSupportObject B (j ≫ f) V E)) b.val := by
    rw [← covarianceSectionMap_restrict B j f F V E D hD a,
      ← covarianceSectionMap_restrict B j f F V E D hD b, h]
  refine ((hid a.val).symm.trans ?_).trans (hid b.val)
  exact congrArg (((openRestrictionIso.{u, v} B j).hom.app F).hom.app
    (op (openCovarianceSupportObject B (j ≫ f) V E))) hinv

end Generator

section Sheafification

variable (B : BigEtaleSite.{u}) {X' X Y : B.Scheme} (j : X' ⟶ X) (f : X ⟶ Y)
  [IsOpenImmersion (B.inclusion.map j)]
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})

/-- The covariance map of finite-support direct-image presheaves is a monomorphism as soon as it
is one over every étale test object. -/
public theorem mono_covariancePresheafMap_of_mono_app
    (h : ∀ V : SmallEtale B Y.obj Y.property, Mono (covariancePresheafApp B j f F V)) :
    Mono (covariancePresheafMap B j f F) := by
  have happ : ∀ V, Mono ((covariancePresheafMap B j f F).app V) := fun V => h V.unop
  exact NatTrans.mono_of_mono_app _

/-- The covariance map of the direct images with compact support is a monomorphism as soon as the
presheaf covariance map is one over every étale test object: the sheaf map is the sheafification
of the presheaf map, and sheafification of abelian sheaves is left exact. -/
public theorem mono_openCovarianceShriekMap_app_of_mono_app
    (h : ∀ V : SmallEtale B Y.obj Y.property, Mono (covariancePresheafApp B j f F V)) :
    Mono ((openCovarianceShriekMap.{u, v} B j f).app F) := by
  have hm : Mono ((openCovariancePresheafMap.{u, v} B j f).val.app F) :=
    mono_covariancePresheafMap_of_mono_app B j f F h
  have he : (openCovarianceShriekMap.{u, v} B j f).app F =
      (presheafToSheaf (SmallEtale.topology B Y.obj Y.property)
          AddCommGrpCat.{max (u + 1) v}).map
        ((openCovariancePresheafMap.{u, v} B j f).val.app F) :=
    Category.id_comp _
  rw [he]
  exact Functor.map_mono _ _

end Sheafification

section Separated

variable (B : BigEtaleSite.{u}) {X' X Y : B.Scheme} (j : X' ⟶ X) (f : X ⟶ Y)
  [IsOpenImmersion (B.inclusion.map j)] [IsSeparated (B.inclusion.map f)]
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})

omit [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)] in
/-- The composite of an open immersion with a separated morphism is separated. -/
public theorem isSeparated_openImmersion_comp : IsSeparated (B.inclusion.map (j ≫ f)) := by
  change IsSeparated (B.inclusion.map j ≫ B.inclusion.map f)
  infer_instance

/-- For a separated morphism the covariance map on finite-support sections over a test object is
injective: a germ in the source colimit is represented over a single eligible support, and both
extension by zero and the transition maps of the target colimit are injective. -/
public theorem covarianceColimitMap_injective (V : SmallEtale B Y.obj Y.property) :
    Function.Injective (covarianceColimitMap B j f F V).hom := by
  have hsep : IsSeparated (B.inclusion.map (j ≫ f)) :=
    isSeparated_openImmersion_comp B j f
  have hfilt' : IsFiltered (FiniteSupport B (j ≫ f) V) :=
    isFiltered_finiteSupport B (j ≫ f) V
  have hfilt : IsFiltered (FiniteSupport B f V) := isFiltered_finiteSupport B f V
  have hpres : PreservesFilteredColimitsOfSize.{u, u} (forget AddCommGrpCat.{max (u + 1) v}) :=
    preservesFilteredColimitsOfSize_of_univLE.{max (u + 1) v, max (u + 1) v, u, u} _
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨E, t, rfl⟩ := Concrete.colimit_exists_rep
    (finiteSupportDiagram B (j ≫ f) ((openRestriction B j).obj F) V) a
  have hgen := ConcreteCategory.congr_hom (covarianceColimitMap_ι B j f F V E) t
  simp only [ConcreteCategory.comp_apply] at hgen
  have hzero : (colimit.ι (finiteSupportDiagram B f F V) (imageFiniteSupport B j f V E))
      (covarianceSectionMap B j f F V E _ (imageFiniteSupport_coe B j f V E) t) = 0 :=
    hgen.symm.trans ha
  obtain ⟨D', i, hD'⟩ := Concrete.addCommGrpCat_colimit_rep_eq_zero.{max (u + 1) v, u, u}
    (finiteSupportDiagram B f F V) (imageFiniteSupport B j f V E) _ hzero
  have hcsm : covarianceSectionMap B j f F V E _ (imageFiniteSupport_coe B j f V E) t = 0 := by
    refine supportedSectionsMap_injective B X.obj X.property F (baseChange B f V)
      (imageFiniteSupport B j f V E).1 D'.1
      (finiteSupport_isLocallyClosed B f V (imageFiniteSupport B j f V E))
      (finiteSupport_isLocallyClosed B f V D') (leOfHom i)
      (finiteSupport_closedWithin B f V (imageFiniteSupport B j f V E) D' (leOfHom i)) ?_
    rw [map_zero]
    exact hD'
  have ht : t = 0 :=
    covarianceSectionMap_injective B j f F V E _ (imageFiniteSupport_coe B j f V E)
      (hcsm.trans (map_zero _).symm)
  rw [ht]
  exact map_zero _

/-- For a separated morphism the covariance map of finite-support direct-image presheaves is a
monomorphism over every étale test object. -/
public theorem mono_covariancePresheafApp (V : SmallEtale B Y.obj Y.property) :
    Mono (covariancePresheafApp B j f F V) := by
  have hcol : Mono (covarianceColimitMap B j f F V) :=
    (AddCommGrpCat.mono_iff_injective _).2 (covarianceColimitMap_injective B j f F V)
  simp only [covariancePresheafApp]
  infer_instance

/-- **Stacks 0F6S, part (4), for a separated morphism.** The covariance map of finite-support
direct-image presheaves attached to an open subscheme of the source is a monomorphism. -/
public theorem mono_covariancePresheafMap : Mono (covariancePresheafMap B j f F) :=
  mono_covariancePresheafMap_of_mono_app B j f F (mono_covariancePresheafApp B j f F)

/-- **Stacks 0F6S, part (4), for a separated morphism.** The covariance map of the direct images
with compact support attached to an open subscheme of the source is a monomorphism: it is the
sheafification of the presheaf covariance map, and sheafification of abelian sheaves is left
exact. -/
@[stacks 0F6S "part (4), injectivity for a separated morphism"]
public theorem mono_openCovarianceShriekMap_app :
    Mono ((openCovarianceShriekMap.{u, v} B j f).app F) :=
  mono_openCovarianceShriekMap_app_of_mono_app B j f F (mono_covariancePresheafApp B j f F)

end Separated

end AlgebraicGeometry.SmallEtale

end
