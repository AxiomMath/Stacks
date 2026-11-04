module

public import StacksFrontier.AlgebraicGeometry.Spaces.TorsionFreeGenericFibrePushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineMonomorphismModuleCounit
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFiniteTypeModuleFinitePresentation

/-!
# The finite type submodules of `j_*F_K` are torsion free (Stacks 0DM0)

Let `f : X ⟶ Y` be a morphism of algebraic spaces, `R` a valuation ring with fraction field `K`,
and `h : U ⟶ T` a morphism of test schemes over `Y` lying over `Spec K ⟶ Spec R`.  The morphism
`j = X_h : X_U ⟶ X_T` of base changes is the inclusion of the generic fibre of `X_T` over
`T = Spec R`.  The proof of Stacks 0DM0 extends a quasi-coherent `𝒪_{X_U}`-module `F_K` by a finite
type quasi-coherent submodule `G ⊂ j_*F_K`, and needs `G` to be flat over `R` and of finite
presentation: "the finite type submodules of `j_*F_K` are torsion free, hence flat over `R`
(Stacks 0539), hence of finite presentation (Stacks 0DLR)".  This file supplies the torsion
freeness, in the form consumed by
`AlgebraicGeometry.Space.isFlatOver_and_isFinitePresentationOnCharts_of_isTorsionFreeOver`, and
the resulting flatness and finite presentation.

Every étale scheme chart of `X_U` maps to `U`, whose scheme is `Spec K`, so the pullback to it of
a nonzero function on `T` is a unit; hence the nonzero functions of `T` act injectively on the
sections of `j_*F_K`, which is therefore torsion free over `T`
(`AlgebraicGeometry.Space.isTorsionFreeOver_modulePushforward_of_valuationRing`), and so is every
submodule of it.

The statements are made for an arbitrary ring map `R ⟶ A` under which the nonzero elements of
`R` become units, the fraction field being the case of interest.

## Main results

* `AlgebraicGeometry.Space.isUnit_appTop_of_isHomLift`: the pullback along `h` of a nonzero
  function on `T` is a unit.
* `AlgebraicGeometry.Space.isTorsionFreeOver_modulePushforward_baseChangeMap_of_isHomLift`:
  `j_*F_K` is torsion free over `T`.
* `AlgebraicGeometry.Space.isTorsionFreeOver_subobject_modulePushforward_baseChangeMap`: every
  submodule of `j_*F_K` is torsion free over `T`.
* `AlgebraicGeometry.Space.isFlatOver_and_isFinitePresentationOnCharts_subobject_pushforward`:
  every finite type quasi-coherent submodule of `j_*F_K` is flat over `T` and of finite
  presentation, when `X_T ⟶ T` is locally of finite presentation.

## References

* [Stacks Project, Tag 0DM0](https://stacks.math.columbia.edu/tag/0DM0)
* [Stacks Project, Tag 0539](https://stacks.math.columbia.edu/tag/0539)
* [Stacks Project, Tag 0DLR](https://stacks.math.columbia.edu/tag/0DLR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The pullback along `Spec A ⟶ Spec R` of a nonzero global function on `Spec R` is a unit, if
the nonzero elements of `R` become units in `A`. -/
theorem isUnit_Spec_map_appTop {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (hRA : ∀ r : R, r ≠ 0 → IsUnit (algebraMap R A r))
    (t : Γ(Spec (CommRingCat.of R), ⊤)) (ht : t ≠ 0) :
    IsUnit ((Spec.map (CommRingCat.ofHom (algebraMap R A))).appTop t) := by
  set t' : R := (Scheme.ΓSpecIso (CommRingCat.of R)).hom t
  have htt' : t = (Scheme.ΓSpecIso (CommRingCat.of R)).inv t' :=
    (Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of R)) t).symm
  have ht' : t' ≠ 0 := fun h0 => ht (by rw [htt', h0, map_zero])
  have hnat := congrArg (fun φ => φ t')
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R A)))
  simp only [ConcreteCategory.comp_apply] at hnat
  rw [htt', ← hnat]
  exact (hRA t' ht').map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom

/-- A morphism of objects of the big fppf site equal, up to the identifications of its source and
target, to the morphism underlying `Spec A ⟶ Spec R`, pulls back nonzero global functions to
units if the nonzero elements of `R` become units in `A`. -/
theorem isUnit_appTop_of_eq_eqToHom {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (hRA : ∀ r : R, r ≠ 0 → IsUnit (algebraMap R A r))
    {hR : B.Contains (Spec (.of R))} {hA : B.Contains (Spec (.of A))} {b : Spec (.of R) ⟶ S}
    {P Q : BigFppfOver B S hS} (ψ : P ⟶ Q)
    (hP : P = siteObject B S hS hA (Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ b))
    (hQ : Q = siteObject B S hS hR b)
    (hψ : ψ = eqToHom hP ≫ (Over.homMk
        (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap R A)))) :
        siteObject B S hS hA (Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ b) ⟶
          siteObject B S hS hR b) ≫ eqToHom hQ.symm)
    (t : Γ((BigFppfOver.toScheme B S hS).obj Q, ⊤)) (ht : t ≠ 0) :
    IsUnit (((BigFppfOver.toScheme B S hS).map ψ).appTop t) := by
  subst hP hQ
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hψ
  subst hψ
  exact isUnit_Spec_map_appTop hRA t ht

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
  (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
  {hR : B.Contains (Spec (.of R))} {hA : B.Contains (Spec (.of A))} {b : Spec (.of R) ⟶ S}
  {U T : SchemesOver Y} (h : U ⟶ T)

/-- **The nonzero functions on `T` pull back to units on `U`.**  For a morphism `h : U ⟶ T` of
test schemes over `Y` lying over `Spec A ⟶ Spec R`, where the nonzero elements of `R` become
units in `A` (for instance `A` the fraction field of a domain `R`), the pullback along `h` of
every nonzero global function on `T` is a unit. -/
theorem isUnit_appTop_of_isHomLift (hRA : ∀ r : R, r ≠ 0 → IsUnit (algebraMap R A r))
    (hh : (CostructuredArrow.proj (schemeSpaceFunctor B S hS) Y).IsHomLift
      (Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap R A)))) :
        siteObject B S hS hA (Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ b) ⟶
          siteObject B S hS hR b) h)
    (t : Γ((BigFppfOver.toScheme B S hS).obj T.left, ⊤)) (ht : t ≠ 0) :
    IsUnit (((BigFppfOver.toScheme B S hS).map h.left).appTop t) := by
  let φ : siteObject B S hS hA (Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ b) ⟶
      siteObject B S hS hR b :=
    Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap R A))))
  exact isUnit_appTop_of_eq_eqToHom hRA h.left
    (IsHomLift.domain_eq (CostructuredArrow.proj (schemeSpaceFunctor B S hS) Y) φ h)
    (IsHomLift.codomain_eq (CostructuredArrow.proj (schemeSpaceFunctor B S hS) Y) φ h)
    (IsHomLift.fac' (CostructuredArrow.proj (schemeSpaceFunctor B S hS) Y) φ h) t ht

/-- The scheme of a test scheme lying over `Spec R` is `Spec R`. -/
noncomputable def isoSpecOfIsHomLift
    (hh : (CostructuredArrow.proj (schemeSpaceFunctor B S hS) Y).IsHomLift
      (Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap R A)))) :
        siteObject B S hS hA (Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ b) ⟶
          siteObject B S hS hR b) h) :
    (BigFppfOver.toScheme B S hS).obj T.left ≅ Spec (CommRingCat.of R) :=
  let φ : siteObject B S hS hA (Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ b) ⟶
      siteObject B S hS hR b :=
    Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap R A))))
  eqToIso (show (BigFppfOver.toScheme B S hS).obj T.left = Spec (CommRingCat.of R) from
    congrArg (BigFppfOver.toScheme B S hS).obj
      (IsHomLift.codomain_eq (CostructuredArrow.proj (schemeSpaceFunctor B S hS) Y) φ h))

/-- **The nonzero functions on `T` pull back to units on every chart of `X_U`.**  For a morphism
`h : U ⟶ T` of test schemes over `Y` lying over `Spec A ⟶ Spec R`, where the nonzero elements of
`R` become units in `A`, every étale scheme chart of `X_U` maps to `T` through `U`, so the
pullback to it of a nonzero global function on `T` is a unit. -/
theorem isUnit_appTop_chart_baseChangeMap_of_isHomLift
    (hRA : ∀ r : R, r ≠ 0 → IsUnit (algebraMap R A r))
    (hh : (CostructuredArrow.proj (schemeSpaceFunctor B S hS) Y).IsHomLift
      (Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap R A)))) :
        siteObject B S hS hA (Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ b) ⟶
          siteObject B S hS hR b) h)
    (U' : SmallEtale B S hS (baseChangeSpace f U).1)
    (γ : (SmallEtale.toOver B S hS (baseChangeSpace f U).1).obj U' ⟶ T.left)
    (hγ : U'.1.hom ≫ (baseChangeMap f h ≫ baseChangeInclusion f T).hom = yoneda.map γ)
    (t : Γ((BigFppfOver.toScheme B S hS).obj T.left, ⊤)) (ht : t ≠ 0) :
    IsUnit (((BigFppfOver.toScheme B S hS).map γ).appTop t) := by
  rw [baseChangeMap_comp_inclusion] at hγ
  let γ₀ : (SmallEtale.toOver B S hS (baseChangeSpace f U).1).obj U' ⟶ U.left :=
    yoneda.preimage (U'.1.hom ≫ (baseChangeInclusion f U).hom)
  have hγ₀ : γ = γ₀ ≫ h.left := by
    refine yoneda.map_injective ?_
    rw [Functor.map_comp, ← hγ]
    show _ = yoneda.map γ₀ ≫ ((schemeSpaceFunctor B S hS).map h.left).hom
    rw [Functor.map_preimage]
    rfl
  rw [hγ₀, Functor.map_comp, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  exact (isUnit_appTop_of_isHomLift R A h hRA hh t ht).map _

/-- **`j_*F_K` is torsion free over `T`.**  Let `R` be a valuation ring, `R ⟶ A` a ring map under
which the nonzero elements of `R` become units (for instance the fraction field of `R`), and
`h : U ⟶ T` a morphism of test schemes over `Y` lying over `Spec A ⟶ Spec R`.  For every
quasi-coherent `𝒪_{X_U}`-module `F`, the direct image `j_*F` along `j = X_h : X_U ⟶ X_T` is
torsion free over `T`. -/
theorem isTorsionFreeOver_modulePushforward_baseChangeMap_of_isHomLift [IsDomain R]
    [ValuationRing R] (hRA : ∀ r : R, r ≠ 0 → IsUnit (algebraMap R A r))
    (hh : (CostructuredArrow.proj (schemeSpaceFunctor B S hS) Y).IsHomLift
      (Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap R A)))) :
        siteObject B S hS hA (Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ b) ⟶
          siteObject B S hS hR b) h)
    (F : Modules.{u, u} B S hS (baseChangeSpace f U).1 (baseChangeSpace f U).2)
    (hF : F.IsQuasicoherentOnSite) :
    IsTorsionFreeOver B S hS (baseChangeSpace f T).2 (baseChangeInclusion f T).hom
      ((modulePushforward B S hS (baseChangeMap f h)).obj F) :=
  isTorsionFreeOver_modulePushforward_of_valuationRing (isoSpecOfIsHomLift R A h hh)
    (baseChangeMap f h) (baseChangeInclusion f T) F
    (isQuasicoherentOnSite_modulePushforward_baseChangeMap_of_isHomLift f R A h hh F hF)
    (isUnit_appTop_chart_baseChangeMap_of_isHomLift f R A h hRA hh)

/-- **Every submodule of `j_*F_K` is torsion free over `T`** (Stacks 0DM0).  Under the hypotheses
of `AlgebraicGeometry.Space.isTorsionFreeOver_modulePushforward_baseChangeMap_of_isHomLift`,
every subobject `G ⊂ j_*F` is torsion free over `T`, in the form consumed by
`AlgebraicGeometry.Space.isFlatOver_and_isFinitePresentationOnCharts_of_isTorsionFreeOver`. -/
theorem isTorsionFreeOver_subobject_modulePushforward_baseChangeMap [IsDomain R]
    [ValuationRing R] (hRA : ∀ r : R, r ≠ 0 → IsUnit (algebraMap R A r))
    (hh : (CostructuredArrow.proj (schemeSpaceFunctor B S hS) Y).IsHomLift
      (Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap R A)))) :
        siteObject B S hS hA (Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ b) ⟶
          siteObject B S hS hR b) h)
    (F : Modules.{u, u} B S hS (baseChangeSpace f U).1 (baseChangeSpace f U).2)
    (hF : F.IsQuasicoherentOnSite)
    (G : Subobject ((modulePushforward B S hS (baseChangeMap f h)).obj F)) :
    IsTorsionFreeOver B S hS (baseChangeSpace f T).2 (baseChangeInclusion f T).hom
      (G : Modules.{u, u} B S hS (baseChangeSpace f T).1 (baseChangeSpace f T).2) :=
  (isTorsionFreeOver_modulePushforward_baseChangeMap_of_isHomLift f R A h hRA hh F hF).subobject G

/-- **The finite type quasi-coherent submodules of `j_*F_K` are flat over `T` and of finite
presentation** (Stacks 0DM0).  Let `R` be a valuation ring, `R ⟶ A` a ring map under which the
nonzero elements of `R` become units, `h : U ⟶ T` a morphism of test schemes over `Y` lying over
`Spec A ⟶ Spec R` such that `X_T ⟶ T` is locally of finite presentation, and `F` a quasi-coherent
`𝒪_{X_U}`-module.  Every finite type quasi-coherent submodule `G ⊂ j_*F`, `j = X_h`, is flat over
`T` (Stacks 05VV) and of finite presentation on the étale scheme charts of `X_T`: it is torsion
free, hence flat by Stacks 0539, hence of finite presentation by Stacks 0DLR. -/
theorem isFlatOver_and_isFinitePresentationOnCharts_subobject_pushforward
    [IsDomain R] [ValuationRing R] (hRA : ∀ r : R, r ≠ 0 → IsUnit (algebraMap R A r))
    (hh : (CostructuredArrow.proj (schemeSpaceFunctor B S hS) Y).IsHomLift
      (Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap R A)))) :
        siteObject B S hS hA (Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ b) ⟶
          siteObject B S hS hR b) h)
    (hfp : IsLocallyOfFinitePresentation B S hS (baseChangeInclusion f T).hom)
    (F : Modules.{u, u} B S hS (baseChangeSpace f U).1 (baseChangeSpace f U).2)
    (hF : F.IsQuasicoherentOnSite)
    (G : Subobject ((modulePushforward B S hS (baseChangeMap f h)).obj F))
    [hGqc : (G : Modules.{u, u} B S hS (baseChangeSpace f T).1
      (baseChangeSpace f T).2).IsQuasicoherentOnSite]
    (hGft : SheafOfModules.IsFiniteTypeOnSite
      (G : Modules.{u, u} B S hS (baseChangeSpace f T).1 (baseChangeSpace f T).2)) :
    IsFlatOver B S hS (baseChangeSpace f T).2 (baseChangeInclusion f T).hom
        (G : Modules.{u, u} B S hS (baseChangeSpace f T).1 (baseChangeSpace f T).2) ∧
      IsFinitePresentationOnCharts B S hS (baseChangeSpace f T).2
        (G : Modules.{u, u} B S hS (baseChangeSpace f T).1 (baseChangeSpace f T).2) :=
  isFlatOver_and_isFinitePresentationOnCharts_of_isTorsionFreeOver (isoSpecOfIsHomLift R A h hh)
    (baseChangeInclusion f T) _ hfp hGft
    (isTorsionFreeOver_subobject_modulePushforward_baseChangeMap f R A h hRA hh F hF G)

end AlgebraicGeometry.Space

end
