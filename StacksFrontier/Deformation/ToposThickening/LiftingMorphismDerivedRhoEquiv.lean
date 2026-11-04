module

public import StacksFrontier.Deformation.ToposThickening.LiftingMorphismDerivedCriterion
public import StacksFrontier.CategoryTheory.Localization.AbsoluteLeftDerivedAdjunction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.CompositionOfToposHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackModulesOfIsoStructureMap

/-!
# The identification of Ext groups in Stacks 0GQ8

Let `f : (Sh(𝒞), 𝒪_𝒞) ⟶ (Sh(ℬ), 𝒪_ℬ)` and `g : (Sh(𝒟), 𝒪_𝒟) ⟶ (Sh(𝒞), 𝒪_𝒞)` be morphisms of
ringed topoi and `𝒢` an `𝒪_𝒟`-module. **Stacks 0GQ8** identifies
`Ext¹_{𝒪_𝒟}(Lg^*NL_{𝒪_𝒞/𝒪_ℬ}, 𝒢) = Ext¹_{g⁻¹𝒪_𝒞}(NL_{g⁻¹𝒪_𝒞/g⁻¹f⁻¹𝒪_ℬ}, 𝒢)`. The map
`Deformation.ToposThickening.LiftingMorphismDerived.rhoClass` between the two groups, built from
the identification of Stacks 08TZ and the derived unit `g⁻¹ ⟶ Lg^*` read over `g⁻¹𝒪_𝒞`, is
bijective, and it carries the images of `ξ` and `ζ` to the classes of the extensions `𝒪'₁` and
`𝒪'₂`.

## Main definitions

* `CategoryTheory.Adjunction.IsUniversal`: a morphism `c ⟶ R d` whose adjunct is invertible.
* `Deformation.ToposThickening.LiftingMorphismDerived.derivedExtendAdjunction`: the derived
  extension of scalars along `g^♯` is left adjoint to restriction of scalars.
* `Deformation.ToposThickening.LiftingMorphismDerived.rhoEquiv`: the identification of Ext
  groups of Stacks 0GQ8.

## Main results

* `Deformation.ToposThickening.LiftingMorphismDerived.isUniversal_derivedUnit_app`: the derived
  unit `g⁻¹M ⟶ Lg^*M` is universal.
* `Deformation.ToposThickening.LiftingMorphismDerived.rhoClass_bijective`: the map `rhoClass` is
  bijective.
* `Deformation.ToposThickening.LiftingMorphismDerived.rhoEquiv_extClass_eq`: `rhoEquiv` carries
  the images of `ξ` and `ζ` to the classes of `𝒪'₁` and `𝒪'₂`.

## References

* [Stacks Project, Tag 0GQ8](https://stacks.math.columbia.edu/tag/0GQ8)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry (RingedTopos RingedToposHom)

universe u v' u' w'

namespace CategoryTheory.Adjunction

/-- **A morphism into a right adjoint whose transpose is an isomorphism is universal.** For an
adjunction `L ⊣ R` and `u : c ⟶ R d` whose adjunct `L c ⟶ d` is invertible, composing with `R`
after `u` is a bijection `(d ⟶ N) ≃ (c ⟶ R N)`. -/
theorem bijective_comp_map_of_isIso {C D : Type*} [Category C] [Category D] {L : C ⥤ D}
    {R : D ⥤ C} (adj : L ⊣ R) {c : C} {d : D} (u : c ⟶ R.obj d)
    [IsIso (L.map u ≫ adj.counit.app d)] (N : D) :
    Function.Bijective (fun e : d ⟶ N => u ≫ R.map e) := by
  have h : (fun e : d ⟶ N ↦ u ≫ R.map e) =
      (adj.homEquiv c N) ∘ (fun e ↦ (L.map u ≫ adj.counit.app d) ≫ e) := by
    funext e
    simp only [Function.comp_apply, Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
    rw [adj.unit_naturality_assoc, Adjunction.right_triangle_components_assoc]
  rw [h]
  exact (adj.homEquiv c N).bijective.comp
    ⟨fun _ _ h ↦ (cancel_epi _).1 h, fun e ↦ ⟨inv (L.map u ≫ adj.counit.app d) ≫ e, by simp⟩⟩

/-- A morphism `u : c ⟶ R d` is **universal** for an adjunction `L ⊣ R` when its adjunct
`L c ⟶ d` is an isomorphism. -/
def IsUniversal {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    {c : C} {d : D} (u : c ⟶ R.obj d) : Prop :=
  IsIso (L.map u ≫ adj.counit.app d)

variable {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)

/-- Precomposing a universal morphism with an isomorphism keeps it universal. -/
theorem IsUniversal.iso_comp {c c' : C} {d : D} {u : c ⟶ R.obj d} (hu : adj.IsUniversal u)
    (i : c' ≅ c) : adj.IsUniversal (i.hom ≫ u) := by
  have : IsIso (L.map u ≫ adj.counit.app d) := hu
  change IsIso (L.map (i.hom ≫ u) ≫ adj.counit.app d)
  rw [L.map_comp, Category.assoc]
  infer_instance

/-- Postcomposing a universal morphism with `R` of an isomorphism keeps it universal. -/
theorem IsUniversal.comp_map_iso {c : C} {d d' : D} {u : c ⟶ R.obj d} (hu : adj.IsUniversal u)
    (j : d ≅ d') : adj.IsUniversal (u ≫ R.map j.hom) := by
  have : IsIso (L.map u ≫ adj.counit.app d) := hu
  change IsIso (L.map (u ≫ R.map j.hom) ≫ adj.counit.app d')
  rw [L.map_comp, Category.assoc,
    show L.map (R.map j.hom) ≫ adj.counit.app d' = adj.counit.app d ≫ j.hom from
      adj.counit_naturality j.hom,
    ← Category.assoc]
  infer_instance

/-- A morphism is universal as soon as its postcomposite with `R` of an isomorphism is. -/
theorem IsUniversal.of_comp_map_iso {c : C} {d d' : D} {u : c ⟶ R.obj d}
    (j : d ≅ d') (hu : adj.IsUniversal (u ≫ R.map j.hom)) : adj.IsUniversal u := by
  have h := hu.comp_map_iso adj j.symm
  rwa [Category.assoc, Iso.symm_hom, ← R.map_comp, Iso.hom_inv_id, R.map_id,
    Category.comp_id] at h

/-- A morphism is universal as soon as its precomposite with an isomorphism is. -/
theorem IsUniversal.of_iso_comp {c c' : C} {d : D} {u : c ⟶ R.obj d} (i : c' ≅ c)
    (hu : adj.IsUniversal (i.hom ≫ u)) : adj.IsUniversal u := by
  have h := hu.iso_comp adj i.symm
  rwa [Iso.symm_hom, Iso.inv_hom_id_assoc] at h

/-- A morphism is universal as soon as it is carried to a universal one by a commuting square
whose horizontal sides are isomorphisms. -/
private theorem IsUniversal.of_comp_map_eq_iso_comp {c c' : C} {d d' : D} {u : c ⟶ R.obj d}
    {u' : c' ⟶ R.obj d'} (hu : adj.IsUniversal u) (i : c' ≅ c) (j : d' ≅ d)
    (h : u' ≫ R.map j.hom = i.hom ≫ u) : adj.IsUniversal u' :=
  of_comp_map_iso adj j ((congrArg adj.IsUniversal h).mpr (hu.iso_comp adj i))

/-- A universal morphism `u : c ⟶ R d` makes `e ↦ u ≫ R e` a bijection. -/
theorem IsUniversal.bijective {c : C} {d : D} {u : c ⟶ R.obj d} (hu : adj.IsUniversal u)
    (N : D) : Function.Bijective (fun e : d ⟶ N => u ≫ R.map e) :=
  have : IsIso (L.map u ≫ adj.counit.app d) := hu
  adj.bijective_comp_map_of_isIso u N

/-- A universal morphism `u : c ⟶ R d` makes `e ↦ u ≫ R e ≫ b` a bijection for every
isomorphism `b`. -/
theorem IsUniversal.bijective_comp_iso {c : C} {d : D} {u : c ⟶ R.obj d} (hu : adj.IsUniversal u)
    {N : D} {N' : C} (b : R.obj N ≅ N') :
    Function.Bijective (fun e : d ⟶ N => u ≫ R.map e ≫ b.hom) := by
  have h : (fun e : d ⟶ N ↦ u ≫ R.map e ≫ b.hom) =
      (fun x ↦ x ≫ b.hom) ∘ (fun e : d ⟶ N ↦ u ≫ R.map e) := by
    funext e
    exact (Category.assoc _ _ _).symm
  rw [h]
  exact Function.Bijective.comp (g := fun x : c ⟶ R.obj N ↦ x ≫ b.hom)
    ⟨fun _ _ h ↦ (cancel_mono b.hom).1 h, fun z ↦ ⟨z ≫ b.inv, by simp⟩⟩ (hu.bijective adj N)

section DerivedUnitComparison

variable {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B] {L : A ⥤ B} {R : B ⥤ A} [L.Additive] [R.Additive]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R] (adj : L ⊣ R)

/-- The localized degreewise unit of an adjunction with exact right adjoint, at a complex `N`,
is the localized unit of the induced adjunction of homotopy categories at the class of `N`,
read through the comparison `Qh ∘ quotient ≅ Q`. -/
theorem quotientCompQhIso_hom_comp_Q_map_unit (N : CochainComplex A ℤ) :
    (DerivedCategory.quotientCompQhIso A).hom.app N ≫
        DerivedCategory.Q.map
            ((adj.mapHomologicalComplexAdjunction (ComplexShape.up ℤ)).unit.app N) ≫
        R.mapDerivedCategoryFactors.inv.app ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj N) =
      DerivedCategory.Qh.map ((adj.mapHomotopyCategoryAdjunction (ComplexShape.up ℤ)).unit.app
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj N)) ≫
        R.mapDerivedCategoryFactorsh.inv.app ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj
          ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj N)) ≫
        R.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso B).hom.app
          ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj N)) := by
  have h := R.mapDerivedCategoryFactorsh_hom_app
    ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj N)
  have h2 : R.mapDerivedCategoryFactorsh.inv.app
        ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj
        ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj N)) ≫
      R.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso B).hom.app
        ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj N)) =
      DerivedCategory.Qh.map ((R.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app
          ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj N)) ≫
        (DerivedCategory.quotientCompQhIso A).hom.app _ ≫
        R.mapDerivedCategoryFactors.inv.app
          ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj N) := by
    rw [← Iso.app_inv, Iso.inv_comp_eq, Iso.app_hom, h]
    simp only [Category.assoc, ← DerivedCategory.Qh.map_comp_assoc, Iso.inv_hom_id_app]
    simp
  have h3 : DerivedCategory.Qh.map ((R.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app
      ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj N)) = 𝟙 _ := by
    simp only [Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_hom]
    exact DerivedCategory.Qh.map_id _
  refine Eq.trans ?_ (congrArg (DerivedCategory.Qh.map
    ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
      ((adj.mapHomologicalComplexAdjunction (ComplexShape.up ℤ)).unit.app N)) ≫ ·) h2).symm
  refine Eq.trans ?_ (congrArg (fun t ↦ DerivedCategory.Qh.map
    ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
      ((adj.mapHomologicalComplexAdjunction (ComplexShape.up ℤ)).unit.app N)) ≫ t ≫ _) h3).symm
  refine Eq.trans ?_ (congrArg (_ ≫ ·) (Category.id_comp _)).symm
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _)
    (DerivedCategory.quotientCompQhIso_hom_naturality
      ((adj.mapHomologicalComplexAdjunction (ComplexShape.up ℤ)).unit.app N)).symm).trans
    (Category.assoc _ _ _))

end DerivedUnitComparison

end CategoryTheory.Adjunction

namespace Deformation.ToposThickening.LiftingMorphismDerived

open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor inverseImageRingSheaf)
open Stacks.Sheaves.RingedToposModules (inverseImageModules extendScalarsFSharp)
open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction (IsKFlat hasResolutions_isKFlat)
open Deformation.ToposThickening.InverseImageExtension (invImage inverseImageRingedTopos
  toInverseImage)

attribute [local instance 10000] HasDerivedCategory.standard

variable {X Y : RingedTopos.{u, u, u}}
  [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (g : RingedToposHom Y X)

/-- Extension of scalars along `g^♯ : g⁻¹𝒪_𝒞 ⟶ 𝒪_𝒟`, the left adjoint of
`extendRestrictAdjunction g`, in the spelling of that adjunction. -/
abbrev extendAlong :=
  Stacks.Sheaves.RingedToposModules.extendScalars Y.J
    (Stacks.Sheaves.RingedToposModules.fSharpCommRing g.toRingedToposModulesHom)
    (inverseImageRingSheaf g.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).property
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property

omit [Y.J.HasSheafCompose (forget AddCommGrpCat)] [X.J.HasSheafCompose (forget AddCommGrpCat)]
  [HasSheafify X.J AddCommGrpCat] [X.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- **Extension of scalars along `g^♯ : g⁻¹𝒪_𝒞 ⟶ 𝒪_𝒟` inverts the quasi-isomorphisms between
K-flat complexes with flat terms.** -/
theorem extendScalarsFSharp_inverts_quasiIso_isKFlat
    {K M : HomotopyCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageRingedTopos g).O))
      (ComplexShape.up ℤ)} (s : K ⟶ M)
    (hs : HomotopyCategory.quasiIso _ (ComplexShape.up ℤ) s)
    (hK : IsKFlat (Y := inverseImageRingedTopos g) K)
    (hM : IsKFlat (Y := inverseImageRingedTopos g) M) :
    IsIso (((extendAlong g).mapHomotopyCategory
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).map s) := by
  obtain ⟨K₀, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  obtain ⟨M₀, rfl⟩ := HomotopyCategory.quotient_obj_surjective M
  obtain ⟨s₀, rfl⟩ : ∃ s₀ : K₀ ⟶ M₀,
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map s₀ = s :=
    ⟨Quot.out s, HomotopyCategory.quotient_map_out s⟩
  have hT := HomotopyCategory.mappingCone_triangleh_distinguished s₀
  have hacyc : (CochainComplex.mappingCone s₀).Acyclic := by
    rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic]
    refine (ObjectProperty.trW_iff_of_distinguished
      (HomotopyCategory.subcategoryAcyclic _) _ hT).1 ?_
    rw [← HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
    exact hs
  have hcone := Stacks.Sheaves.RingedToposDerivedPullback.isKFlat_mappingCone
    (Y := inverseImageRingedTopos g) s₀ hK hM
  have hcyc := Stacks.Sheaves.DerivedPullback.KFlatPullback.cyclesIsFlat
    (inverseImageRingedTopos g) (CochainComplex.mappingCone s₀) hacyc
    ((Stacks.SheafOfModules.KFlat.kFlat_iff_kFlatBifunctor _ _).2 hcone.1) hcone.2
  have hext : (((extendAlong g).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (CochainComplex.mappingCone s₀ : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageRingedTopos g).O)) ℤ)).Acyclic :=
    CochainComplex.acyclic_mapHomologicalComplex_of_cyclesShortExact
      (extendAlong g) _
      fun _ j hij ↦ Stacks.Sheaves.RingedToposModules.shortExact_map_extendScalarsFSharp
        g.toRingedToposModulesHom _
        (HomologicalComplex.cyclesShortComplex_shortExact _ hij (hacyc j)) (hcyc j)
  have hFT := ((extendAlong g).mapHomotopyCategory
    (ComplexShape.up ℤ)).map_distinguished _ hT
  have h3 : HomotopyCategory.subcategoryAcyclic _
      (((extendAlong g).mapHomotopyCategory
        (ComplexShape.up ℤ)).obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          (CochainComplex.mappingCone s₀ : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageRingedTopos g).O)) ℤ))) :=
    ObjectProperty.prop_of_iso _
      ((((extendAlong g).mapHomotopyCategoryFactors
        (ComplexShape.up ℤ)).app (CochainComplex.mappingCone s₀ : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageRingedTopos g).O)) ℤ)).symm)
      ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).2 hext)
  have hq : HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)
      (((extendAlong g).mapHomotopyCategory
        (ComplexShape.up ℤ)).map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map s₀)) := by
    rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
    exact (ObjectProperty.trW_iff_of_distinguished
      (HomotopyCategory.subcategoryAcyclic _) _ hFT).2 h3
  exact Localization.inverts DerivedCategory.Qh
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) _ hq

/-- Extension of scalars along `g^♯`, on the unbounded homotopy category, followed by
localization, has a left derived functor. -/
instance hasPointwiseLeftDerivedFunctor_extendScalarsFSharp :
    ((extendAlong g).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
        (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) :=
  LeftDerivedByResolutions.hasPointwiseLeftDerivedFunctor_of_resolutions _
    (IsKFlat (Y := inverseImageRingedTopos g))
    (hasResolutions_isKFlat (Y := inverseImageRingedTopos g))
    _ (fun s hs hK hM ↦ extendScalarsFSharp_inverts_quasiIso_isKFlat g s hs hK hM)

/-- **The derived extension of scalars along `g^♯ : g⁻¹𝒪_𝒞 ⟶ 𝒪_𝒟`**,
`L(𝒪_𝒟 ⊗_{g⁻¹𝒪_𝒞} -) : D(g⁻¹𝒪_𝒞) ⥤ D(𝒪_𝒟)`. -/
abbrev derivedExtend :=
  ((extendAlong g).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalLeftDerived DerivedCategory.Qh
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))

/-- **The derived extension of scalars is left adjoint to restriction of scalars on derived
categories.** -/
def derivedExtendAdjunction : derivedExtend g ⊣ restrictDerived g :=
  (extendRestrictAdjunction g).derivedMapDerivedCategoryOfResolutions
    (IsKFlat (Y := inverseImageRingedTopos g))
    (hasResolutions_isKFlat (Y := inverseImageRingedTopos g))
    (fun s hs hK hM ↦ extendScalarsFSharp_inverts_quasiIso_isKFlat g s hs hK hM)

section KFlatInverseImage

variable [Y.J.HasSheafCompose (forget CommRingCat.{u})]

/-- The structure map `g⁻¹𝒪_𝒞 ⟶ g⁻¹𝒪_𝒞` of `(Sh(𝒟), g⁻¹𝒪_𝒞) ⟶ (Sh(𝒞), 𝒪_𝒞)` is an
isomorphism. -/
instance isIso_toInverseImage_fSharpInverseImage :
    IsIso (toInverseImage g).fSharpInverseImage := by
  rw [Deformation.ToposThickening.InverseImageExtension.toInverseImage_fSharpInverseImage]
  exact IsIso.id _

omit [Y.J.HasSheafCompose (forget AddCommGrpCat)] [X.J.HasSheafCompose (forget AddCommGrpCat)]
  [HasSheafify X.J AddCommGrpCat] [X.J.WEqualsLocallyBijective AddCommGrpCat]
  [HasSheafify Y.J AddCommGrpCat] [Y.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- The structure map of `(Sh(𝒟), g⁻¹𝒪_𝒞) ⟶ (Sh(𝒞), 𝒪_𝒞)`, read as a morphism of sheaves of
rings, is the identity. -/
theorem toInverseImage_fSharpInverseImageRing :
    (toInverseImage g).fSharpInverseImageRing = 𝟙 _ := by
  rw [← AlgebraicGeometry.RingedToposHom.forgetCommRingSheaf_map_fSharpInverseImage,
    Deformation.ToposThickening.InverseImageExtension.toInverseImage_fSharpInverseImage]
  exact (Stacks.forgetCommRingSheaf Y.J).map_id _

/-- **Pullback of sheaves of modules along `(Sh(𝒟), g⁻¹𝒪_𝒞) ⟶ (Sh(𝒞), 𝒪_𝒞)` is the inverse
image `g⁻¹`.** -/
def pullbackModulesToInverseImageIso :
    (toInverseImage g).toModulesHom.pullbackModules ≅
      inverseImageModules g.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  Functor.isoWhiskerLeft _
    ((Stacks.Sheaves.RingedToposModules.RingedToposHom.extendScalarsFSharpIsoRestrictScalarsOfIsIso
      (toInverseImage g).toModulesHom) ≪≫
      eqToIso (by
        have h' : (asIso (toInverseImage g).fSharpInverseImageRing).inv = 𝟙 _ :=
          (asIso_inv _).trans (IsIso.inv_eq_of_hom_inv_id
            ((Category.comp_id _).trans (toInverseImage_fSharpInverseImageRing g)))
        change SheafOfModules.restrictScalars
          (asIso (toInverseImage g).fSharpInverseImageRing).inv = _
        rw [h']
        rfl)) ≪≫
    Functor.rightUnitor _

/-- **The inverse image `g⁻¹` preserves K-flat complexes with flat terms** (Stacks 0G7E along
`(Sh(𝒟), g⁻¹𝒪_𝒞) ⟶ (Sh(𝒞), 𝒪_𝒞)`). -/
theorem isKFlat_inverseImage
    (P : HomotopyCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ))
    (hP : IsKFlat (Y := X) P) :
    IsKFlat (Y := inverseImageRingedTopos g)
      (((inverseImageModules g.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomotopyCategory
        (ComplexShape.up ℤ)).obj P) := by
  obtain ⟨P₀, rfl⟩ := HomotopyCategory.quotient_obj_surjective P
  have : (toInverseImage g).toModulesHom.pullbackModules.Additive :=
    AlgebraicGeometry.RingedToposHom.pullbackModules_additive _
  have : (inverseImageModules g.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).Additive :=
    CategoryTheory.Sheaf.inverseImageTargetModules_additive.{u, u, u, u, u, u} Y.J X.J g.toToposHom
      (B := X.O)
  have h := Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom.isKFlat_pullbackMapHomotopy
    (toInverseImage g) _ hP
  have e : ((toInverseImage g).toModulesHom.pullbackModules.mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P₀ ≅
      ((inverseImageModules g.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P₀ :=
    HomologicalComplex.Hom.isoOfComponents
      (fun i ↦ (pullbackModulesToInverseImageIso g).app (P₀.X i))
      (fun i j _ ↦ ((pullbackModulesToInverseImageIso g).hom.naturality (P₀.d i j)).symm)
  refine ⟨CochainComplex.KFlatBifunctor.KFlat.of_iso _ h.1 e, fun i ↦ ?_⟩
  exact (exactFunctor _ _).prop_of_iso
    ((Stacks.SheafOfModules.Tensor.sheafTensor _).flip.mapIso
      ((HomologicalComplex.eval _ _ i).mapIso e)) (h.2 i)

end KFlatInverseImage

section Universal

/-- The derived extension of scalars on the class of a complex, compared with the class of the
degreewise extension. -/
abbrev derivedExtendCounit :=
  ((extendAlong g).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalLeftDerivedCounit DerivedCategory.Qh
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))

/-- The unit of extension and restriction of scalars along `g^♯`, on homotopy categories and
localized, read through the comparison of the restriction of scalars of derived categories. -/
abbrev localizedUnit
    (Z : HomotopyCategory (SheafOfModules.{u}
      (inverseImageRingSheaf g.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
      (ComplexShape.up ℤ)) :=
  DerivedCategory.Qh.map
      (((extendRestrictAdjunction g).mapHomotopyCategoryAdjunction
        (ComplexShape.up ℤ)).unit.app Z) ≫
    (restrictAlong g).mapDerivedCategoryFactorsh.inv.app
      (((extendAlong g).mapHomotopyCategory (ComplexShape.up ℤ)).obj Z)

omit [Y.J.HasSheafCompose (forget AddCommGrpCat)] [X.J.HasSheafCompose (forget AddCommGrpCat)]
  [HasSheafify X.J AddCommGrpCat] [X.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- **The adjunct of the localized unit is the comparison of the derived extension of scalars.**
-/
theorem map_localizedUnit_comp_counit
    (Z : HomotopyCategory (SheafOfModules.{u}
      (inverseImageRingSheaf g.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
      (ComplexShape.up ℤ)) :
    (derivedExtend g).map (localizedUnit g Z) ≫ (derivedExtendAdjunction g).counit.app _ =
      (derivedExtendCounit g).app Z := by
  have := Functor.isRightDerivedFunctor_mapDerivedCategory_of_exact (restrictAlong g)
  have := Functor.isRightDerivedFunctor_mapDerivedCategory_comp_of_exact (restrictAlong g)
    (derivedExtend g)
  have hfac : (derivedExtend g).map ((restrictAlong g).mapDerivedCategoryFactorsh.inv.app
        (((extendAlong g).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj Z)) ≫
      (derivedExtendAdjunction g).counit.app (DerivedCategory.Qh.obj
        (((extendAlong g).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj Z)) =
      (derivedExtendCounit g).app (((restrictAlong g).mapHomotopyCategory (ComplexShape.up ℤ)).obj
        (((extendAlong g).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj Z)) ≫
        DerivedCategory.Qh.map
          (((extendRestrictAdjunction g).mapHomotopyCategoryAdjunction
            (ComplexShape.up ℤ)).counit.app
            (((extendAlong g).mapHomotopyCategory
              (ComplexShape.up ℤ)).obj Z)) :=
    Adjunction.derivedε_fac_app (W₂ := HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.Sheaves.RingedToposModules.commRingSheaf Y.J Y.O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property)) (ComplexShape.up ℤ)) _ _ _ _
  have hnat := (derivedExtendCounit g).naturality
    (((extendRestrictAdjunction g).mapHomotopyCategoryAdjunction (ComplexShape.up ℤ)).unit.app Z)
  have htri := ((extendRestrictAdjunction g).mapHomotopyCategoryAdjunction
    (ComplexShape.up ℤ)).left_triangle_components Z
  rw [localizedUnit, Functor.map_comp, Category.assoc, hfac]
  refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hnat)).trans ?_
  rw [Category.assoc, Functor.comp_map, ← DerivedCategory.Qh.map_comp, htri]
  exact (congrArg (_ ≫ ·) (DerivedCategory.Qh.map_id _)).trans (Category.comp_id _)

omit [Y.J.HasSheafCompose (forget AddCommGrpCat)] [X.J.HasSheafCompose (forget AddCommGrpCat)]
  [HasSheafify X.J AddCommGrpCat] [X.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- **The localized unit is universal at a K-flat complex with flat terms.** -/
theorem isUniversal_localizedUnit
    (Z : HomotopyCategory (SheafOfModules.{u}
      (inverseImageRingSheaf g.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
      (ComplexShape.up ℤ))
    (hZ : IsKFlat (Y := inverseImageRingedTopos g) Z) :
    (derivedExtendAdjunction g).IsUniversal (localizedUnit g Z) := by
  change IsIso (_ ≫ _)
  rw [map_localizedUnit_comp_counit]
  exact LeftDerivedByResolutions.isIso_app_of_resolutions
    (HomotopyCategory.quasiIso (SheafOfModules.{u}
      (Stacks.Sheaves.RingedToposModules.commRingSheaf Y.J
        (Stacks.Sheaves.RingedToposModules.inverseImageStructureCommRing g.toRingedToposModulesHom)
        (inverseImageRingSheaf g.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).property))
      (ComplexShape.up ℤ))
    (IsKFlat (Y := inverseImageRingedTopos g))
    (hasResolutions_isKFlat (Y := inverseImageRingedTopos g))
    _ (fun s hs hK hM ↦ extendScalarsFSharp_inverts_quasiIso_isKFlat g s hs hK hM)
    DerivedCategory.Qh (derivedExtend g) (derivedExtendCounit g) Z hZ

/-- The degreewise unit on a complex, localized: `Q(g⁻¹K) ⟶ res Q(g^*K)`. -/
abbrev localizedUnitComplex
    (K₀ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :=
  DerivedCategory.Q.map (pullbackUnitComplex g K₀) ≫
    (restrictDerivedFactors g).inv.app
      ((g.toRingedToposModulesHom.pullbackModules.mapHomologicalComplex (ComplexShape.up ℤ)).obj K₀)

omit [HasSheafify X.J AddCommGrpCat] [X.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- The localized degreewise unit on a complex is the localized unit on its homotopy class, read
through the comparison `Qh ∘ quotient ≅ Q`. -/
theorem quotientCompQhIso_hom_comp_localizedUnitComplex
    (K₀ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    (DerivedCategory.quotientCompQhIso _).hom.app
        (((inverseImageModules g.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K₀) ≫
      localizedUnitComplex g K₀ =
    localizedUnit g ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        (((inverseImageModules g.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K₀)) ≫
      (restrictDerived g).map ((DerivedCategory.quotientCompQhIso _).hom.app
        ((g.toRingedToposModulesHom.pullbackModules.mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K₀)) := by
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  exact Adjunction.quotientCompQhIso_hom_comp_Q_map_unit (extendRestrictAdjunction g)
    (((inverseImageModules g.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K₀)

variable [Y.J.HasSheafCompose (forget CommRingCat.{u})]

/-- **The localized degreewise unit is universal at a K-flat complex with flat terms.** -/
theorem isUniversal_localizedUnitComplex
    (K₀ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hK : IsKFlat (Y := X) ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K₀)) :
    (derivedExtendAdjunction g).IsUniversal (localizedUnitComplex g K₀) := by
  have hZ := isKFlat_inverseImage g _ hK
  have h1 := (isUniversal_localizedUnit g ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
    (((inverseImageModules g.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K₀)) hZ).comp_map_iso (derivedExtendAdjunction g)
    ((DerivedCategory.quotientCompQhIso _).app
      ((g.toRingedToposModulesHom.pullbackModules.mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K₀))
  rw [Iso.app_hom, ← quotientCompQhIso_hom_comp_localizedUnitComplex] at h1
  exact h1.of_iso_comp _ ((DerivedCategory.quotientCompQhIso _).app
    (((inverseImageModules g.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K₀))

/-- **The derived unit `g⁻¹ ⟶ Lg^*` is universal at a K-flat complex with flat terms.** -/
theorem isUniversal_derivedUnit_app_Q
    (K₀ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hK : IsKFlat (Y := X) ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K₀)) :
    (derivedExtendAdjunction g).IsUniversal ((derivedUnit g).app (DerivedCategory.Q.obj K₀)) := by
  have : IsIso (derivedPullbackComparisonComplex g K₀) := by
    rw [derivedPullbackComparisonComplex_eq]
    open Stacks.Cohomology.DerivedPullbackCompositionOfToposHom in
    have := isIso_derivedPullbackComparison_app_isKFlat g _ hK
    infer_instance
  let j := asIso (derivedPullbackComparisonComplex g K₀)
  refine (isUniversal_localizedUnitComplex g K₀ hK).of_comp_map_eq_iso_comp _
    ((inverseImageModules g.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapDerivedCategoryFactors.app K₀)
    j ?_
  rw [localizedUnitComplex, ← derivedUnit_app_Q g K₀]
  simp only [j, asIso_hom, Iso.app_hom, Category.assoc]
  erw [Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app, Category.comp_id]
  rfl

/-- **The derived unit `g⁻¹ ⟶ Lg^*` is universal**: its adjunct
`L(𝒪_𝒟 ⊗_{g⁻¹𝒪_𝒞} -)(g⁻¹M) ⟶ Lg^*M` is an isomorphism for every `M` in `D(𝒪_𝒞)`. -/
theorem isUniversal_derivedUnit_app
    (M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (derivedExtendAdjunction g).IsUniversal ((derivedUnit g).app M) := by
  obtain ⟨P, hP, s, hs⟩ := hasResolutions_isKFlat (Y := X)
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj (DerivedCategory.Q.objPreimage M))
  obtain ⟨K₀, rfl⟩ := HomotopyCategory.quotient_obj_surjective P
  have : IsIso (DerivedCategory.Qh.map s) :=
    Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) _ hs
  let i : DerivedCategory.Q.obj K₀ ≅ M :=
    (DerivedCategory.quotientCompQhIso _).symm.app K₀ ≪≫ asIso (DerivedCategory.Qh.map s) ≪≫
      (DerivedCategory.quotientCompQhIso _).app _ ≪≫ DerivedCategory.Q.objObjPreimageIso M
  have hnat := (derivedUnit g).naturality i.inv
  simp only [Functor.comp_map] at hnat
  exact (isUniversal_derivedUnit_app_Q g K₀ hP).of_comp_map_eq_iso_comp _
    ((invImageDerived g).mapIso i.symm) ((derivedPullback g).mapIso i.symm) hnat.symm

end Universal

section RhoEquiv

open Deformation.ToposThickening.RingedToposExtensionProblem (ofTrivialBase)
open Deformation.ToposThickening.InverseImageExtension (baseIso restrictedIdeal pushoutSolution
  pullbackSolution)

variable {B : RingedTopos.{v', u', w'}} [B.J.HasSheafCompose (forget RingCat.{w'})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Y.J.HasSheafCompose (forget CommRingCat.{u})]
  [HasWeakSheafify Y.J CommRingCat.{u}] [HasWeakSheafify X.J CommRingCat.{u}]
  {f : RingedToposHom X B}
  {G : SheafOfModules.{u} ((sheafCompose Y.J (forget₂ CommRingCat.{u} RingCat.{u})).obj Y.O)}

/-- The change of base ring along `(f ∘ g)⁻¹𝒪_ℬ ≅ g⁻¹f⁻¹𝒪_ℬ` is an isomorphism of naive
cotangent complexes (Stacks 08TX for a square of isomorphisms). -/
instance isIso_baseIsoChange : IsIso (baseIsoChange (f := f) g) := by
  unfold baseIsoChange Stacks.SheafOfModules.naiveCotangentComplexMapOfBase
  exact Stacks.SheafOfModules.isIso_naiveCotangentComplexMapOfSquare.{u, u, u, u} Y.J _ _ _ _ _ _
    (baseIso f g).symm (Iso.refl _) _

/-- **The map `rhoClass` is bijective.** -/
theorem rhoClass_bijective : Function.Bijective (rhoClass (f := f) (G := G) g) := by
  have pre : ∀ {𝒞 : Type (u + 1)} [Category.{u + 1} 𝒞] {P Q Z : 𝒞} (a : P ≅ Q),
      Function.Bijective (fun x : Q ⟶ Z ↦ a.hom ≫ x) :=
    fun a ↦ (Iso.homFromEquiv a.symm).bijective
  let a₁ := asIso (baseIsoChange (f := f) g)
  exact (pre (DerivedCategory.Q.mapIso a₁)).comp
    ((pre (DerivedCategory.Q.mapIso
      (Stacks.SheafOfModules.inverseImageNaiveCotangentComplexIso.{u, u, u, u, u, u}
      Y.J X.J g.toToposHom (A := (inverseImageCommRingFunctor f.toToposHom).obj B.O) (B := X.O)
      f.fSharpInverseImage).symm)).comp
    ((pre ((inverseImageModules g.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapDerivedCategoryFactors.app _).symm).comp
    ((isUniversal_derivedUnit_app g _).bijective_comp_iso (derivedExtendAdjunction g)
      (((restrictAlong g).mapDerivedCategory.commShiftIso (1 : ℤ)).app _ ≪≫
        (shiftFunctor (DerivedCategory (SheafOfModules.{u}
          (inverseImageRingSheaf g.toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) (1 : ℤ)).mapIso
          (((restrictAlong g).mapDerivedCategorySingleFunctor 0).app G)))))

/-- **The identification of Ext groups**
`Ext¹_{𝒪_𝒟}(Lg^*NL_{𝒪_𝒞/𝒪_ℬ}, 𝒢) = Ext¹_{g⁻¹𝒪_𝒞}(NL_{g⁻¹𝒪_𝒞/g⁻¹f⁻¹𝒪_ℬ}, 𝒢)`, the base of the
right-hand side read as `(f ∘ g)⁻¹𝒪_ℬ ≅ g⁻¹f⁻¹𝒪_ℬ`: the bijection `rhoClass`, which sends
`e : Lg^*NL_{𝒪_𝒞/𝒪_ℬ} ⟶ 𝒢[1]` to the composite of the identification
`NL_{g⁻¹𝒪_𝒞/g⁻¹f⁻¹𝒪_ℬ} ≅ g⁻¹NL_{𝒪_𝒞/𝒪_ℬ}` of Stacks 08TZ, the derived unit
`g⁻¹NL_{𝒪_𝒞/𝒪_ℬ} ⟶ Lg^*NL_{𝒪_𝒞/𝒪_ℬ}` read over `g⁻¹𝒪_𝒞` (the tensor-hom adjunction along
`g^♯`) and `e` read over `g⁻¹𝒪_𝒞`. -/
@[stacks 0GQ8]
def rhoEquiv :
    DerivedCategory.Ext ((derivedPullback g).obj (DerivedCategory.Q.obj
        (Stacks.SheafOfModules.naiveCotangentComplex.{u, u, u, u} X.J
          ((inverseImageCommRingFunctor f.toToposHom).obj B.O) X.O f.fSharpInverseImage)))
      ((DerivedCategory.singleFunctor _ 0).obj G) 1 ≃
    DerivedCategory.Ext (DerivedCategory.Q.obj
        (Stacks.SheafOfModules.naiveCotangentComplex.{u, u, u, u} Y.J
        ((inverseImageCommRingFunctor (f.comp (toInverseImage g)).toToposHom).obj B.O)
        ((invImage g).obj X.O) (f.comp (toInverseImage g)).fSharpInverseImage))
      ((DerivedCategory.singleFunctor (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf ((invImage g).obj X.O))) 0).obj
          (restrictedIdeal g G)) 1 :=
  Equiv.ofBijective (rhoClass g) (rhoClass_bijective g)

/-- The identification of Stacks 0GQ8 is `rhoClass`. -/
theorem rhoEquiv_apply
    (e : DerivedCategory.Ext ((derivedPullback g).obj (DerivedCategory.Q.obj
        (Stacks.SheafOfModules.naiveCotangentComplex.{u, u, u, u} X.J
          ((inverseImageCommRingFunctor f.toToposHom).obj B.O) X.O f.fSharpInverseImage)))
      ((DerivedCategory.singleFunctor _ 0).obj G) 1) :
    rhoEquiv g e = rhoClass g e :=
  rfl

variable [Y.J.WEqualsLocallyBijective CommRingCat.{u}] [HasWeakSheafify Y.J AddCommGrpCat.{u}]
  {F : SheafOfModules.{u} ((sheafCompose X.J (forget₂ CommRingCat.{u} RingCat.{u})).obj X.O)}
  (QC : (ofTrivialBase f F).CompatibleFirstOrderThickening)
  (QD : (ofTrivialBase (f.comp g) G).CompatibleFirstOrderThickening)
  (c : g.toRingedToposModulesHom.pullbackModules.obj F ⟶ G)

/-- **The classes of `𝒪'₁` and `𝒪'₂`.** Under the identification `rhoEquiv` of
`Ext¹_{𝒪_𝒟}(Lg^*NL_{𝒪_𝒞/𝒪_ℬ}, 𝒢)` with `Ext¹_{g⁻¹𝒪_𝒞}(NL_{g⁻¹𝒪_𝒞/g⁻¹f⁻¹𝒪_ℬ}, 𝒢)`, the image of
`ξ` (the class of `QC`, through `Lg^*` and `Lg^*ℱ ⟶ g^*ℱ ⟶ 𝒢`) is the class (Stacks 0GQ5) of the
pushout `𝒪'₁` of `g⁻¹𝒪_{𝒞'}` along `c`, and the image of `ζ` (the class of `QD`, through
`Lg^*NL_{𝒪_𝒞/𝒪_ℬ} ⟶ NL_{𝒪_𝒟/𝒪_ℬ}`) is the class of the pullback `𝒪'₂` of `𝒪_{𝒟'}` along
`g^♯`. -/
@[stacks 0GQ8]
theorem rhoEquiv_extClass_eq :
    rhoEquiv g (pullbackExtClass g c
        (RingedToposExtensionProblem.squareZeroExtensionClassesEquiv f F
          (Quotient.mk
            (RingedToposExtensionProblem.CompatibleFirstOrderThickening.isomorphicSetoid _)
            QC))) =
      RingedToposExtensionProblem.squareZeroExtensionClassesEquiv (f.comp (toInverseImage g))
        (restrictedIdeal g G)
        (Quotient.mk (RingedToposExtensionProblem.CompatibleFirstOrderThickening.isomorphicSetoid _)
          (pushoutSolution g QC QD c)) ∧
    rhoEquiv g (restrictExtClass f g
        (RingedToposExtensionProblem.squareZeroExtensionClassesEquiv (f.comp g) G
          (Quotient.mk
            (RingedToposExtensionProblem.CompatibleFirstOrderThickening.isomorphicSetoid _)
            QD))) =
      RingedToposExtensionProblem.squareZeroExtensionClassesEquiv (f.comp (toInverseImage g))
        (restrictedIdeal g G)
        (Quotient.mk (RingedToposExtensionProblem.CompatibleFirstOrderThickening.isomorphicSetoid _)
          (pullbackSolution g QC QD c)) :=
  ⟨rhoClass_pullbackExtClass_eq g QC QD c, rhoClass_restrictExtClass_eq g QC QD c⟩

end RhoEquiv

end Deformation.ToposThickening.LiftingMorphismDerived
