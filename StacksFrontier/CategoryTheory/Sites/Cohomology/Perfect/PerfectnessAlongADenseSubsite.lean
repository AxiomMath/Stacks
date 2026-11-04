module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BaseChangeUnitor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DenseSubsiteModules
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedPoint
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentDenseSubsite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectnessAlongACocontinuousFunctor

/-!
# Perfectness along the Comparison Lemma for sheaves of modules

Let `(C', K, 𝒪)` be a ringed site and let `v : C ⥤ C'` exhibit `(C, J)` as a dense subsite of
`(C', K)`. Restricting `𝒪` along `v` gives a ringed site `(C, J, 𝒪|_C)`, and restriction of
sections along `v` is an equivalence of the categories of sheaves of modules (the Comparison
Lemma, `Stacks.DenseSubsiteModules.moduleRestrictionEquivalence`). This file proves that the
induced equivalence of derived categories preserves perfect objects in both directions, and that
restriction of scalars along an isomorphism of structure sheaves does too.

Perfectness (Stacks 08G5) is local: an object is perfect when, locally on the site, it is
represented by a strictly perfect complex. Both directions are instances of the two transfer
principles of
`StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectnessAlongACocontinuousFunctor` and
`StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectnessAlongAnExactFunctor`: the slice
of a dense subsite is a dense subsite (`Stacks.Sites.overPost_isDenseSubsite`), and the
Comparison Lemma commutes with restriction to slices on the nose
(`Stacks.DenseSubsiteModules.moduleRestriction_comp_overFunctor`).

## Main results

* `AlgebraicGeometry.RingedSite.isPerfect_mapDerivedCategory_moduleRestriction`: restriction to a
  dense subsite preserves perfect objects.
* `AlgebraicGeometry.RingedSite.isPerfect_mapDerivedCategory_moduleRestrictionEquivalence_inverse`:
  so does the inverse of the Comparison Lemma.
* `AlgebraicGeometry.RingedSite.isPerfect_mapDerivedCategory_restrictScalars_of_iso`:
  restriction of scalars along an isomorphism of structure sheaves preserves perfect objects.

## References

* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
* [Stacks Project, Tag 03A0](https://stacks.math.columbia.edu/tag/03A0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.DenseSubsiteModules

universe uX vX uY vY w dX dY

namespace AlgebraicGeometry.RingedSite

/-- **The ringed site induced on a dense subsite.**  For `v : C ⥤ C'` with `(C, J)` a dense
subsite of the site of the ringed site `Y`, the site `(C, J)` with the restriction of the structure
sheaf of `Y` along `v`. -/
abbrev denseSubsiteRestriction (Y : RingedSite.{uY, vY, w}) {𝒞 : Type uX} [Category.{vX} 𝒞]
    (J : GrothendieckTopology 𝒞) (v : 𝒞 ⥤ Y.C) [v.IsDenseSubsite J Y.J] :
    RingedSite.{uX, vX, w} where
  C := 𝒞
  J := J
  O := (v.sheafPushforwardContinuous CommRingCat.{w} J Y.J).obj Y.O

section DenseSubsite

attribute [local instance] Stacks.Sites.overPost_isDenseSubsite

variable (Y : RingedSite.{uY, vY, w}) {𝒞 : Type uX} [Category.{vX} 𝒞]
  (J : GrothendieckTopology 𝒞) (v : 𝒞 ⥤ Y.C) [v.IsDenseSubsite J Y.J]
  [(v.sheafPushforwardContinuous AddCommGrpCat.{w} J Y.J).IsEquivalence]
  [∀ W : 𝒞, ((Over.post (X := W) v).sheafPushforwardContinuous AddCommGrpCat.{w}
    (J.over W) (Y.J.over (v.obj W))).IsEquivalence]

/-- Restriction of sheaves of modules to a dense subsite, as a functor into the sheaves of modules
of the induced ringed site. -/
abbrev denseSubsiteModuleRestriction :
    SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⥤
      SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf
        (Y.denseSubsiteRestriction J v).O) :=
  moduleRestriction J Y.J v (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)

/-- The Comparison Lemma for sheaves of modules, with target the sheaves of modules of the
induced ringed site. -/
abbrev denseSubsiteModulesEquiv :
    SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ≌
      SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf
        (Y.denseSubsiteRestriction J v).O) :=
  moduleRestrictionEquivalence J Y.J v (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)

/-- Restriction of sheaves of modules to a dense subsite is an equivalence of categories. -/
instance isEquivalence_denseSubsiteModuleRestriction :
    (Y.denseSubsiteModuleRestriction J v).IsEquivalence :=
  (Y.denseSubsiteModulesEquiv J v).isEquivalence_functor

/-- Restriction of sheaves of modules to a dense subsite is an additive functor. -/
instance additive_denseSubsiteModuleRestriction :
    (Y.denseSubsiteModuleRestriction J v).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The inverse of the Comparison Lemma for sheaves of modules is an additive functor. -/
instance additive_denseSubsiteModulesEquiv_inverse :
    (Y.denseSubsiteModulesEquiv J v).inverse.Additive :=
  have : (Y.denseSubsiteModulesEquiv J v).functor.Additive :=
    (inferInstance : (Y.denseSubsiteModuleRestriction J v).Additive)
  inferInstance

/-- The slice of the Comparison Lemma: restriction of sheaves of modules over `v W` to the slice
dense subsite `Over W ⥤ Over (v W)`. -/
abbrev sliceModuleRestriction (W : 𝒞) :
    SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over (v.obj W)) ⥤
      SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf
        (Y.denseSubsiteRestriction J v).O).over W) :=
  moduleRestriction (J.over W) (Y.J.over (v.obj W)) (Over.post (X := W) v)
    ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over (v.obj W))

/-- The slice of the Comparison Lemma, as an equivalence. -/
abbrev sliceModulesEquiv (W : 𝒞) :
    SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over (v.obj W)) ≌
      SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf
        (Y.denseSubsiteRestriction J v).O).over W) :=
  moduleRestrictionEquivalence (J.over W) (Y.J.over (v.obj W))
    (Over.post (X := W) v) ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over (v.obj W))

/-- Restriction of sheaves of modules to the slice dense subsite is an equivalence of
categories. -/
instance isEquivalence_sliceModuleRestriction (W : 𝒞) :
    (Y.sliceModuleRestriction J v W).IsEquivalence :=
  (Y.sliceModulesEquiv J v W).isEquivalence_functor

/-- Restriction of sheaves of modules to the slice dense subsite is an additive functor. -/
instance additive_sliceModuleRestriction (W : 𝒞) :
    (Y.sliceModuleRestriction J v W).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Restriction to a dense subsite carries the unit module to the unit module. -/
def sliceModuleRestrictionUnitIso (W : 𝒞) :
    (Y.sliceModuleRestriction J v W).obj
        (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over (v.obj W))) ≅
      SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
        (Y.denseSubsiteRestriction J v).O).over W) :=
  Iso.refl _

variable [∀ U : 𝒞, HasSheafify (J.over U) AddCommGrpCat.{w}]
  [∀ U : 𝒞, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ W : Y.C, HasSheafify (Y.J.over W) AddCommGrpCat.{w}]
  [∀ W : Y.C, (Y.J.over W).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasDerivedCategory.{dY} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
  [HasDerivedCategory.{dX} (SheafOfModules.{w}
    (Stacks.SheafOfModules.Tensor.ringSheaf (Y.denseSubsiteRestriction J v).O))]

/-- **Restriction to a dense subsite preserves perfect objects.** -/
theorem isPerfect_mapDerivedCategory_moduleRestriction
    (E : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (hE : Y.IsPerfect E) :
    (Y.denseSubsiteRestriction J v).IsPerfect
      ((Y.denseSubsiteModuleRestriction J v).mapDerivedCategory.obj E) :=
  isPerfect_mapDerivedCategory_of_isCocontinuous_of_sliceFunctors
    (X := Y.denseSubsiteRestriction J v) (Y := Y) v
    (Y.denseSubsiteModuleRestriction J v)
    (fun W => Y.sliceModuleRestriction J v W) (fun W => Y.sliceModuleRestrictionUnitIso J v W)
    (fun _ => Iso.refl _) E hE

/-- **The inverse of the Comparison Lemma preserves perfect objects.** -/
theorem isPerfect_mapDerivedCategory_moduleRestrictionEquivalence_inverse
    (E : DerivedCategory (SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf (Y.denseSubsiteRestriction J v).O)))
    (hE : (Y.denseSubsiteRestriction J v).IsPerfect E) :
    Y.IsPerfect ((Y.denseSubsiteModulesEquiv J v).inverse.mapDerivedCategory.obj E) := by
  let e := Y.denseSubsiteModulesEquiv J v
  have hadd : ∀ W, (Y.sliceModulesEquiv J v W).inverse.Additive := fun W =>
    have : (Y.sliceModulesEquiv J v W).functor.Additive :=
      (inferInstance : (Y.sliceModuleRestriction J v W).Additive)
    inferInstance
  have : v.IsCoverDense Y.J := Functor.IsDenseSubsite.isCoverDense J Y.J v
  exact isPerfect_mapDerivedCategory (X := Y) (Y := Y.denseSubsiteRestriction J v) v e.inverse
    (hGadd := hadd) (hGlim := fun _ => inferInstance) (hGcolim := fun _ => inferInstance)
    (fun W => (Y.sliceModulesEquiv J v W).inverse) (fun U => Y.J.superset_covering
      (S := Sieve.coverByImage v U) (R := Sieve.ofObjects v.obj U)
      (fun _ _ ⟨h⟩ => ⟨h.obj, ⟨h.lift⟩⟩) (v.is_cover_of_isCoverDense Y.J U))
    (fun W => (Y.sliceModulesEquiv J v W).inverse.mapIso
        (Y.sliceModuleRestrictionUnitIso J v W).symm ≪≫
      (Y.sliceModulesEquiv J v W).unitIso.symm.app _)
    (fun W => (Functor.leftUnitor _).symm ≪≫ Functor.isoWhiskerRight e.counitIso.symm _ ≪≫
      Functor.isoWhiskerLeft e.inverse
        (Functor.isoWhiskerLeft (SheafOfModules.overFunctor.{w}
            (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) (v.obj W))
            (Y.sliceModulesEquiv J v W).unitIso.symm ≪≫
          Functor.rightUnitor _)) E hE

end DenseSubsite

section RestrictScalars

variable {𝒞 : Type uX} [Category.{vX} 𝒞] {J : GrothendieckTopology 𝒞}
  {R S : Sheaf J RingCat.{w}}

/-- The section of the unit sheaf of modules over a sheaf of rings `R`, read through restriction
of scalars along `α : S ⟶ R`, is the image under `α` of the corresponding section of `S`. -/
theorem unitToRestrictScalarsUnit_val_app (α : S ⟶ R) (V : 𝒞ᵒᵖ) (r : S.obj.obj V) :
    PresheafOfModules.Hom.app
        (Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit α).val V r =
      α.hom.app V r := by
  have h := ((PresheafOfModules.Hom.app
      (Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit α).val V).hom.map_smul r
        (1 : S.obj.obj V))
  rw [Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit_val_app_one] at h
  exact (congrArg _ (mul_one r).symm).trans (h.trans (mul_one (α.hom.app V r)))

/-- Along an isomorphism `α : S ⟶ R` of sheaves of rings, restriction of scalars carries the unit
sheaf of modules to the unit sheaf of modules. -/
instance isIso_unitToRestrictScalarsUnit (α : S ⟶ R) [IsIso α] :
    IsIso (Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit α) := by
  let φ := Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit α
  have hb (V : 𝒞ᵒᵖ) : Function.Bijective (PresheafOfModules.Hom.app φ.val V) := by
    have hα : Function.Bijective (α.hom.app V) :=
      (ConcreteCategory.isIso_iff_bijective (α.hom.app V)).1 inferInstance
    have : (PresheafOfModules.Hom.app φ.val V : S.obj.obj V → R.obj.obj V) = α.hom.app V :=
      funext (unitToRestrictScalarsUnit_val_app α V)
    exact this ▸ hα
  have : Mono φ.val := PresheafOfModules.mono_of_injective (f := φ.val) fun {V} => (hb V).1
  have : Epi φ.val := PresheafOfModules.epi_of_surjective (f := φ.val) fun {V} => (hb V).2
  have : IsIso ((SheafOfModules.forget _).map φ) := isIso_of_mono_of_epi φ.val
  exact isIso_of_reflects_iso φ (SheafOfModules.forget _)

/-- Restriction of scalars along an isomorphism of sheaves of rings is an equivalence. -/
instance isEquivalence_restrictScalars_of_isIso (α : S ⟶ R) [IsIso α] :
    (SheafOfModules.restrictScalars.{w} α).IsEquivalence :=
  (Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso (asIso α).symm).isEquivalence_functor

/-- Along an isomorphism `e : S ≅ R` of sheaves of rings, restriction of scalars carries the unit
sheaf of modules to the unit sheaf of modules. -/
def restrictScalarsUnitIsoOfIso (e : S ≅ R) :
    (SheafOfModules.restrictScalars e.hom).obj (SheafOfModules.unit R) ≅ SheafOfModules.unit S :=
  (asIso (Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit e.hom)).symm

end RestrictScalars

/-- The ringed site with the site of `X` and the structure sheaf `O'`. -/
abbrev withStructureSheaf (X : RingedSite.{uX, vX, w}) (O' : Sheaf X.J CommRingCat.{w}) :
    RingedSite.{uX, vX, w} where
  C := X.C
  J := X.J
  O := O'

section RingIso

variable (X : RingedSite.{uX, vX, w}) (O' : Sheaf X.J CommRingCat.{w})
  (e : Stacks.SheafOfModules.Tensor.ringSheaf O' ≅ Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{w}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasDerivedCategory.{dX} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  [HasDerivedCategory.{dY} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O'))]

/-- **Restriction of scalars along an isomorphism of structure sheaves preserves perfect
objects.** -/
theorem isPerfect_mapDerivedCategory_restrictScalars_of_iso
    (E : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hE : X.IsPerfect E) :
    (X.withStructureSheaf O').IsPerfect
      ((SheafOfModules.restrictScalars.{w} e.hom).mapDerivedCategory.obj E) := by
  let eW : ∀ W : X.C, _ := fun W => (X.J.overPullback RingCat.{w} W).mapIso e
  exact isPerfect_mapDerivedCategory (X := X.withStructureSheaf O') (Y := X) (𝟭 X.C)
    (SheafOfModules.restrictScalars.{w} e.hom)
    (fun W => SheafOfModules.restrictScalars.{w} (eW W).hom)
    (fun U => X.J.superset_covering (fun V _ _ => ⟨V, ⟨𝟙 V⟩⟩) (X.J.top_mem U))
    (fun W => restrictScalarsUnitIsoOfIso (eW W)) (fun _ => Iso.refl _) E hE

end RingIso

end AlgebraicGeometry.RingedSite

end
