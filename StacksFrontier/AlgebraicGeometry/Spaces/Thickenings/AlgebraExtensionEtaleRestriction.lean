module

public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsEtaleSourceLocalization
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.InverseImageStructureSheafMap
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RepresentedCoherator
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleIsoCongr
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtalePostcompCocontinuous
public import StacksFrontier.Cotangent.Spaces.EtaleRestriction
public import StacksFrontier.Deformation.AlgebraExtension.SiteRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.Topology.Dimension.KrullSupplement

/-!
# Restricting extensions of `f⁻¹𝒪_Y`-algebras along an étale morphism

Let `a : U ⟶ X` be an étale morphism of algebraic spaces over `S` and let `f : X ⟶ Y`. An
extension `0 ⟶ ℳ ⟶ 𝒪' ⟶ 𝒪_X ⟶ 0` of `f⁻¹𝒪_Y`-algebras on the small étale site of `X`
restricts along the postcomposition functor `U_étale ⟶ X_étale` of Stacks 03LP to an extension
of `(a ≫ f)⁻¹𝒪_Y`-algebras of `𝒪_U` on the small étale site of `U`: restriction along that
functor is the inverse image along `a` (Stacks 03LV), which carries `𝒪_X` to `𝒪_U` and
`f⁻¹𝒪_Y` to `(a ≫ f)⁻¹𝒪_Y` (Stacks 03G8), compatibly with the structure maps.

For an isomorphism `a` this is the transport of extensions between isomorphic algebraic spaces,
which is how extensions living on a closed fibre `X' ×_{Spec A} Spec k` of a deformation are
read on the space `X₀` it deforms.

## Main definitions

* `AlgebraicGeometry.Space.etaleRestrictionRingComparison`: the comparison of
  `(a ≫ f)⁻¹𝒪_Y ⟶ 𝒪_U` with the restriction of `f⁻¹𝒪_Y ⟶ 𝒪_X`.
* `AlgebraicGeometry.Space.etaleRestrictionModule`: the restriction of an `𝒪_X`-module, read as
  an `𝒪_U`-module.
* `AlgebraicGeometry.Space.etaleRestrictionFunctor`: restriction of extensions, as a functor.

## References

* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
* [Stacks Project, Tag 03LV](https://stacks.math.columbia.edu/tag/03LV)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.Sheaves.ToposPullback

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {U X Y : AlgebraicSpaces B S hS} (a : U ⟶ X) (ha : IsEtale B S hS a.hom) (f : X ⟶ Y)

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for `PreservesFiniteProducts` of this pushforward on small étale sites is deep
/-- Restriction of sheaves of sets along the postcomposition functor of an étale morphism
preserves finite products (it is a right adjoint); found directly, as instance search times out
on it under Lean v4.35.0. -/
local instance (priority := high)
    preservesFiniteProducts_smallEtalePostcomp_AlgebraExtensionEtaleRestriction :
    Limits.PreservesFiniteProducts ((smallEtalePostcomp B S hS a ha).sheafPushforwardContinuous
      (Type u) (SmallEtale.topology B S hS U.1) (SmallEtale.topology B S hS X.1)) :=
  inferInstance

/-- **The ring data of étale restriction.** Restriction along the postcomposition functor of
an étale `a : U ⟶ X` carries `f^♯ : f⁻¹𝒪_Y ⟶ 𝒪_X` to `(a ≫ f)^♯ : (a ≫ f)⁻¹𝒪_Y ⟶ 𝒪_U`, up to
the identifications `a⁻¹f⁻¹𝒪_Y ≅ (a ≫ f)⁻¹𝒪_Y` of Stacks 03G8 and `a⁻¹𝒪_X ≅ 𝒪_U` of
Stacks 03LV. -/
def etaleRestrictionRingComparison :
    Deformation.AlgebraExtension.RingComparison (G := smallEtalePostcomp B S hS a ha)
      (K := SmallEtale.topology B S hS U.1) (J := SmallEtale.topology B S hS X.1)
      (structureSharpInverseImage B S hS f) (structureSharpInverseImage B S hS (a ≫ f)) where
  α := (inverseImageStructureSheafCompIso B S hS a f).symm ≪≫
    inverseImageCommRingRestrictionIso (SmallEtale.topology B S hS U.1)
      (SmallEtale.topology B S hS X.1) (smallEtalePostcomp B S hS a ha)
      (smallEtaleRingedToposHom B S hS a).toToposHom
      (smallToposMorphismTypeU_inverseImageIso B S hS a ha) (inverseImageStructureSheaf B S hS f)
  ω := (etaleRestrictionStructureSheafIso B S hS a ha).symm
  comm := by
    have hnat := inverseImageCommRingRestrictionIso_naturality (SmallEtale.topology B S hS U.1)
      (SmallEtale.topology B S hS X.1) (smallEtalePostcomp B S hS a ha)
      (smallEtaleRingedToposHom B S hS a).toToposHom
      (smallToposMorphismTypeU_inverseImageIso B S hS a ha) (structureSharpInverseImage B S hS f)
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, etaleRestrictionStructureSheafIso,
      Iso.trans_inv, Iso.symm_inv]
    rw [← hnat, ← Category.assoc, ← Category.assoc]
    congr 1
    rw [Iso.eq_inv_comp, ← Category.assoc, ← inverseImageStructureSharp_square B S hS a ha f,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The ring data of étale restriction followed by the restricted structure map `f^♯` and
`a⁻¹𝒪_X ≅ 𝒪_U` is the structure map `(a ≫ f)^♯`. -/
theorem etaleRestrictionRingComparison_α_hom_comp_reduction :
    (etaleRestrictionRingComparison B S hS a ha f).α.hom ≫
        (Deformation.AlgebraExtension.ringRes (SmallEtale.topology B S hS U.1)
          (smallEtalePostcomp B S hS a ha)).map (structureSharpInverseImage B S hS f) ≫
        (etaleRestrictionStructureSheafIso B S hS a ha).hom =
      structureSharpInverseImage B S hS (a ≫ f) := by
  rw [← Category.assoc, ← (etaleRestrictionRingComparison B S hS a ha f).comm]
  exact (Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) (etaleRestrictionStructureSheafIso B S hS a ha).inv_hom_id).trans
      (Category.comp_id _))

/-- **The ring data of étale restriction is compatible with the maps
`(i ≫ g)⁻¹𝒪_Y ⟶ i⁻¹𝒪_{X'}`**: restricting the map along `g` read on `i` and comparing both ends
with inverse images along `a` gives the map along `g` read on `a ≫ i`. -/
theorem etaleRestrictionRingComparison_α_map_inverseImageStructureSheafMap
    {X' : AlgebraicSpaces B S hS} (i : X ⟶ X') (g : X' ⟶ Y) :
    (etaleRestrictionRingComparison B S hS a ha (i ≫ g)).α.hom ≫
        (Deformation.AlgebraExtension.ringRes (SmallEtale.topology B S hS U.1)
          (smallEtalePostcomp B S hS a ha)).map (inverseImageStructureSheafMap B S hS i g) ≫
        (etaleRestrictionRingComparison B S hS a ha i).α.inv =
      inverseImageStructureSheafMap B S hS (a ≫ i) g := by
  have hn := inverseImageCommRingRestrictionIso_naturality (SmallEtale.topology B S hS U.1)
    (SmallEtale.topology B S hS X.1) (smallEtalePostcomp B S hS a ha)
    (smallEtaleRingedToposHom B S hS a).toToposHom
    (smallToposMorphismTypeU_inverseImageIso B S hS a ha) (inverseImageStructureSheafMap B S hS i g)
  refine Eq.trans ?_ (inverseImageStructureSheafMap_inverseImage B S hS a i g)
  simp only [etaleRestrictionRingComparison, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Iso.symm_inv, Category.assoc]
  refine congrArg (_ ≫ ·) ?_
  rw [← reassoc_of% hn, Iso.hom_inv_id_assoc]
  rfl

section InverseImageMap

variable {X₁ X' X'₁ : AlgebraicSpaces B S hS} (i : X ⟶ X') (a₁ : U ⟶ X₁)
  (ha₁ : IsEtale B S hS a₁.hom) (i₁ : X₁ ⟶ X'₁) (φ : X'₁ ⟶ X') (tri : (a₁ ≫ i₁) ≫ φ = a ≫ i)

/-- **The map of restricted inverse images along a morphism under `U`.** For étale `a : U ⟶ X`,
`a₁ : U ⟶ X₁`, morphisms `i : X ⟶ X'`, `i₁ : X₁ ⟶ X'₁` and `φ : X'₁ ⟶ X'` with
`a₁ ≫ i₁ ≫ φ = a ≫ i`, the map `(i⁻¹𝒪_{X'})|_U ⟶ (i₁⁻¹𝒪_{X'₁})|_U` of the restrictions along
`a` and `a₁`: through `(i⁻¹𝒪_{X'})|_U ≅ (a ≫ i)⁻¹𝒪_{X'}` (Stacks 03G8, 03LQ) it is the map
`(a₁ ≫ i₁ ≫ φ)⁻¹𝒪_{X'} ⟶ (a₁ ≫ i₁)⁻¹𝒪_{X'₁}` of `φ^♯`. -/
def etaleRestrictionInverseImageMap :
    (Deformation.AlgebraExtension.ringRes (SmallEtale.topology B S hS U.1)
        (smallEtalePostcomp B S hS a ha)).obj (inverseImageStructureSheaf B S hS i) ⟶
      (Deformation.AlgebraExtension.ringRes (SmallEtale.topology B S hS U.1)
        (smallEtalePostcomp B S hS a₁ ha₁)).obj (inverseImageStructureSheaf B S hS i₁) :=
  (etaleRestrictionRingComparison B S hS a ha i).α.inv ≫
    inverseImageStructureSheafMapOfEq B S hS (a₁ ≫ i₁) φ tri ≫
    (etaleRestrictionRingComparison B S hS a₁ ha₁ i₁).α.hom

/-- The map of restricted inverse images is compatible with the restricted structure maps. -/
theorem etaleRestrictionInverseImageMap_comp_reduction :
    etaleRestrictionInverseImageMap B S hS a ha i a₁ ha₁ i₁ φ tri ≫
        (Deformation.AlgebraExtension.ringRes (SmallEtale.topology B S hS U.1)
          (smallEtalePostcomp B S hS a₁ ha₁)).map (structureSharpInverseImage B S hS i₁) ≫
        (etaleRestrictionStructureSheafIso B S hS a₁ ha₁).hom =
      (Deformation.AlgebraExtension.ringRes (SmallEtale.topology B S hS U.1)
          (smallEtalePostcomp B S hS a ha)).map (structureSharpInverseImage B S hS i) ≫
        (etaleRestrictionStructureSheafIso B S hS a ha).hom := by
  simp only [etaleRestrictionInverseImageMap, Category.assoc]
  rw [etaleRestrictionRingComparison_α_hom_comp_reduction,
    inverseImageStructureSheafMapOfEq_comp_structureSharpInverseImage, Iso.inv_comp_eq,
    etaleRestrictionRingComparison_α_hom_comp_reduction]

/-- **The map of restricted inverse images is compatible with the algebra structures**: for
`g : X' ⟶ Y` and `g₁ = φ ≫ g`, it carries the restriction of the map along `g` read on `i` to
that of the map along `g₁` read on `i₁`. -/
theorem etaleRestrictionInverseImageMap_algebraMap (g : X' ⟶ Y) (g₁ : X'₁ ⟶ Y)
    (hg : φ ≫ g = g₁) (h : a ≫ i ≫ g = a₁ ≫ i₁ ≫ g₁) :
    (etaleRestrictionRingComparison B S hS a ha (i ≫ g)).α.hom ≫
        (Deformation.AlgebraExtension.ringRes (SmallEtale.topology B S hS U.1)
          (smallEtalePostcomp B S hS a ha)).map (inverseImageStructureSheafMap B S hS i g) ≫
        etaleRestrictionInverseImageMap B S hS a ha i a₁ ha₁ i₁ φ tri =
      eqToHom (congrArg (inverseImageStructureSheaf B S hS) h) ≫
        (etaleRestrictionRingComparison B S hS a₁ ha₁ (i₁ ≫ g₁)).α.hom ≫
        (Deformation.AlgebraExtension.ringRes (SmallEtale.topology B S hS U.1)
          (smallEtalePostcomp B S hS a₁ ha₁)).map (inverseImageStructureSheafMap B S hS i₁ g₁) := by
  subst hg
  have hR := etaleRestrictionRingComparison_α_map_inverseImageStructureSheafMap B S hS a ha i g
  have hR₁ := etaleRestrictionRingComparison_α_map_inverseImageStructureSheafMap B S hS a₁ ha₁
    i₁ (φ ≫ g)
  have hc := inverseImageStructureSheafMapOfEq_comp B S hS (a₁ ≫ i₁) φ g tri rfl
  have hR₁' : (etaleRestrictionRingComparison B S hS a₁ ha₁ (i₁ ≫ φ ≫ g)).α.hom ≫
      (Deformation.AlgebraExtension.ringRes (SmallEtale.topology B S hS U.1)
        (smallEtalePostcomp B S hS a₁ ha₁)).map (inverseImageStructureSheafMap B S hS i₁ (φ ≫ g)) =
      inverseImageStructureSheafMap B S hS (a₁ ≫ i₁) (φ ≫ g) ≫
        (etaleRestrictionRingComparison B S hS a₁ ha₁ i₁).α.hom :=
    (Iso.comp_inv_eq _).mp ((Category.assoc _ _ _).trans hR₁)
  have h0 : inverseImageStructureSheafMapOfEq B S hS (a ≫ i) g rfl =
      inverseImageStructureSheafMap B S hS (a ≫ i) g :=
    Category.id_comp _
  unfold etaleRestrictionInverseImageMap
  rw [hR₁', reassoc_of% hR, ← h0, reassoc_of% hc]
  exact Category.assoc _ _ _

end InverseImageMap

/-- **Restriction of `𝒪_X`-modules along an étale `a : U ⟶ X`, as `𝒪_U`-modules.** The sections
over a chart `V` of `U` are the sections over the chart `V ⟶ U ⟶ X` of `X`, with `𝒪_U` acting
through `a⁻¹𝒪_X ≅ 𝒪_U`. -/
abbrev etaleRestrictionModule :
    SheafOfModules.{u} ((sheafCompose (SmallEtale.topology B S hS X.1)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj (smallEtaleRingedTopos B S hS X).O) ⥤
    SheafOfModules.{u} ((sheafCompose (SmallEtale.topology B S hS U.1)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj (smallEtaleRingedTopos B S hS U).O) :=
  SheafOfModules.pushforward.{u}
    ((sheafCompose (SmallEtale.topology B S hS U.1) (forget₂ CommRingCat.{u} RingCat.{u})).map
      (etaleRestrictionStructureSheafIso B S hS a ha).inv)

/-- The restriction of an `𝒪_X`-module along an étale `a`, as a comparison of modules over the
ring data of `AlgebraicGeometry.Space.etaleRestrictionRingComparison`: its sections are those of
the module, unchanged. -/
def etaleRestrictionModuleComparison
    (M : SheafOfModules.{u} ((sheafCompose (SmallEtale.topology B S hS X.1)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj (smallEtaleRingedTopos B S hS X).O)) :
    Deformation.AlgebraExtension.ModuleComparison (G := smallEtalePostcomp B S hS a ha)
      (K := SmallEtale.topology B S hS U.1) (J := SmallEtale.topology B S hS X.1)
      (etaleRestrictionRingComparison B S hS a ha f).ω M
      ((etaleRestrictionModule B S hS a ha).obj M) where
  μ _ := AddEquiv.refl _
  μ_naturality _ _ := rfl
  μ_smul _ _ _ := rfl

/-- **Restriction of extensions along an étale morphism.** For an étale `a : U ⟶ X` and any
`f : X ⟶ Y`, an extension of `f⁻¹𝒪_Y`-algebras of `𝒪_X` by `ℳ` restricts to an extension of
`(a ≫ f)⁻¹𝒪_Y`-algebras of `𝒪_U` by the restriction of `ℳ`. -/
abbrev etaleRestrictionFunctor
    (M : SheafOfModules.{u} ((sheafCompose (SmallEtale.topology B S hS X.1)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj (smallEtaleRingedTopos B S hS X).O)) :
    Deformation.AlgebraExtension (J := SmallEtale.topology B S hS X.1)
        (structureSharpInverseImage B S hS f) M ⥤
      Deformation.AlgebraExtension (J := SmallEtale.topology B S hS U.1)
        (structureSharpInverseImage B S hS (a ≫ f))
        ((etaleRestrictionModule B S hS a ha).obj M) :=
  Deformation.AlgebraExtension.restrictViaFunctor (G := smallEtalePostcomp B S hS a ha)
    (K := SmallEtale.topology B S hS U.1) (J := SmallEtale.topology B S hS X.1)
    (structureSharpInverseImage B S hS (a ≫ f)) ((etaleRestrictionModule B S hS a ha).obj M)
    (etaleRestrictionRingComparison B S hS a ha f)
    (etaleRestrictionModuleComparison B S hS a ha f M)

/-! ### Isomorphisms -/

section Iso

variable {B S hS}

variable (B S hS)

/-- Postcomposition with an isomorphism of algebraic spaces exhibits the small étale site of the
source as a dense subsite of that of the target. -/
theorem isDenseSubsite_smallEtalePostcomp_of_iso (e : U ≅ X) :
    (smallEtalePostcomp B S hS e.hom (isEtale_hom_of_iso B S hS e)).IsDenseSubsite
      (SmallEtale.topology B S hS U.1) (SmallEtale.topology B S hS X.1) :=
  SmallEtale.congr_functor_isDenseSubsite B S hS ((ObjectProperty.ι _).mapIso e)

/-- Restriction of extensions along an isomorphism of algebraic spaces is fully faithful. -/
theorem fullyFaithful_etaleRestrictionFunctor_of_iso (e : U ≅ X)
    (M : SheafOfModules.{u} ((sheafCompose (SmallEtale.topology B S hS X.1)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj (smallEtaleRingedTopos B S hS X).O)) :
    (etaleRestrictionFunctor B S hS e.hom (isEtale_hom_of_iso B S hS e) f M).Full ∧
      (etaleRestrictionFunctor B S hS e.hom (isEtale_hom_of_iso B S hS e) f M).Faithful := by
  have := isDenseSubsite_smallEtalePostcomp_of_iso B S hS e
  have : (smallEtalePostcomp B S hS e.hom (isEtale_hom_of_iso B S hS e)).EssSurj :=
    inferInstanceAs (SmallEtale.congr B S hS ((ObjectProperty.ι _).mapIso e)).functor.EssSurj
  exact ⟨inferInstance, inferInstance⟩

end Iso

/-! ### Changing the base map along an equality -/

/-- An extension of `f⁻¹𝒪_Y`-algebras of `𝒪_X` read as one of `f'⁻¹𝒪_Y`-algebras along an equality
`f = f'` of morphisms of algebraic spaces. The middle term, reduction and ideal are unchanged; the
algebra structure is composed with the identification `f'⁻¹𝒪_Y = f⁻¹𝒪_Y`. -/
def castBase {f f' : U ⟶ Y} (h : f = f')
    {M : SheafOfModules.{u} ((sheafCompose (SmallEtale.topology B S hS U.1)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj (smallEtaleRingedTopos B S hS U).O)}
    (P : Deformation.AlgebraExtension (J := SmallEtale.topology B S hS U.1)
      (structureSharpInverseImage B S hS f) M) :
    Deformation.AlgebraExtension (J := SmallEtale.topology B S hS U.1)
      (structureSharpInverseImage B S hS f') M where
  extension := P.extension
  reduction := P.reduction
  locallySurjective := P.locallySurjective
  squareZero := P.squareZero
  algebraMap := eqToHom (congrArg (inverseImageStructureSheaf B S hS) h.symm) ≫ P.algebraMap
  algebraMap_reduction := (Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) P.algebraMap_reduction).trans
      (structureSharpInverseImage_eqToHom B S hS h.symm))
  kernelInclusion := P.kernelInclusion
  kernelZero := P.kernelZero
  kernelUniversal := P.kernelUniversal

end AlgebraicGeometry.Space

end
