module

public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedPicardFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.ReprFpqcFullness
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.RepresentedBaseEffectivity

/-!
# The polarized families of the relatively ample locus: full faithfulness

Fix an object `X₀ ⟶ V₀` of `Spaces'_{fp, flat, proper}` over the big fppf site of `Spec(ℤ)`. The
functor `AlgebraicGeometry.amplePolarizedFunctor` from the relatively ample locus of
`Picardstack_{X₀/V₀}` to the polarized families over `X₀` is fully faithful.

A morphism of the Picard stack is determined by its morphism of test schemes and its comparison
of modules, and the comparison is recovered from the comparison of polarizations on the scheme
models, because the reading of quasi-coherent modules on represented algebraic spaces as modules
on schemes is bijective on morphisms
(`AlgebraicGeometry.Space.QuasiCoherentDescent.bijective_representedZariski_map`) and the inverse
image along an isomorphism of algebraic spaces is an equivalence. Conversely a morphism of
polarized families over `X₀` lies over a morphism of test schemes over `V₀`
(`AlgebraicGeometry.ampleBase`), its morphism of total spaces is the morphism of scheme models of
that morphism (`AlgebraicGeometry.totalMap_eq_ampleModelBaseMap`, since a morphism into `X_T` is
determined by its two projections), and its comparison of polarizations is reflected to a
comparison of modules (`AlgebraicGeometry.ampleHomOf`).

## Main results

* `AlgebraicGeometry.amplePolarizedHom_injective`: the morphism of polarized families determines
  the morphism of the Picard stack.
* `AlgebraicGeometry.amplePolarizedHom_ampleHomOf`: every morphism of polarized families over
  `X₀` comes from a morphism of the Picard stack.
* `AlgebraicGeometry.faithful_amplePolarizedFunctor` and
  `AlgebraicGeometry.full_amplePolarizedFunctor`: the functor is fully faithful.

## References

* [Stacks Project, Tag 0D41](https://stacks.math.columbia.edu/tag/0D41)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {B : BigFppfSite.{u}} {X₀ : CartesianProperFlatSpaces B integerBase B.contains_integerBase}
  {hc : Space.ModulePushforwardCoherence B integerBase B.contains_integerBase}

variable {A C : Space.PicardObject (properFlatPicardSituation X₀)}
  {hA : Space.picardAmple hc (properFlatPicardSituation X₀) A}
  {hC : Space.picardAmple hc (properFlatPicardSituation X₀) C}

/-- Two isomorphisms with the same composite with a fixed isomorphism agree. -/
theorem Iso.trans_left_cancel {C₀ : Type*} [Category* C₀] {X Y Z : C₀} (e : X ≅ Y)
    {f g : Y ≅ Z} (h : e ≪≫ f = e ≪≫ g) : f = g := by
  simpa only [Iso.symm_self_id_assoc] using congrArg (fun k => e.symm ≪≫ k) h

/-- A faithful functor is injective on isomorphisms. -/
theorem Functor.mapIso_injective {C₀ D₀ : Type*} [Category* C₀] [Category* D₀]
    (F : C₀ ⥤ D₀) [F.Faithful] {X Y : C₀} {e e' : X ≅ Y} (h : F.mapIso e = F.mapIso e') :
    e = e' :=
  Iso.ext (F.map_injective (congrArg Iso.hom h))

/-- Two isomorphisms with equal images under a composite of functors injective on the relevant
morphisms agree. -/
theorem Functor.mapIso_injective_of_injective {C₀ D₀ E₀ : Type*} [Category* C₀] [Category* D₀]
    [Category* E₀] (F : C₀ ⥤ D₀) (G : D₀ ⥤ E₀) {X Y : C₀}
    (hinj : Function.Injective (fun ψ : X ⟶ Y => G.map (F.map ψ))) {e e' : X ≅ Y}
    (h : G.mapIso (F.mapIso e) = G.mapIso (F.mapIso e')) : e = e' :=
  Iso.ext (hinj (congrArg Iso.hom h))

/-- `AlgebraicGeometry.Space.QuasiCoherentDescent.bijective_representedZariski_map`, with the
modules read as `𝒪`-modules on the represented algebraic space. -/
theorem bijective_representedZariski_map_space {S : Scheme.{u}} {hS : B.Contains S}
    (U : BigFppfOver B S hS)
    (M N : Space.Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))
    (hM : M.IsQuasicoherentOnSite) :
    Function.Bijective (fun ψ : M ⟶ N =>
      (SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property).map
        ((Space.representedSmallEtaleModuleEquivalence B S hS U).inverse.map ψ)) :=
  Space.QuasiCoherentDescent.bijective_representedZariski_map B S hS M N hM

/-- The inverse image of the module of `ampleModel hC` along a morphism of scheme models is
quasi-coherent. -/
private theorem isQuasicoherentOnSite_modulePullback_ampleModelModule
    (m : ampleModel hA ⟶ ampleModel hC) :
    ((Space.modulePullback B integerBase B.contains_integerBase
      (Space.representedSpaceMap B integerBase B.contains_integerBase m)).obj
        (ampleModelModule hC)).IsQuasicoherentOnSite :=
  Space.isQuasicoherentOnSite_modulePullback_representedSpaceMap B integerBase
    B.contains_integerBase m
    (Space.relativelyRepresentable_yoneda_map B integerBase B.contains_integerBase _) _
    (isQuasicoherentOnSite_ampleModelModule hC)

/-- **The morphism of polarized families determines the morphism of the Picard stack.** -/
theorem amplePolarizedHom_injective {m m' : Space.PicardHom A C}
    (h : amplePolarizedHom hA hC m = amplePolarizedHom hA hC m') : m = m' := by
  obtain ⟨g, fib, hfib⟩ := m
  obtain ⟨g', fib', hfib'⟩ := m'
  have hg : g = g' :=
    CostructuredArrow.hom_ext _ _ (Over.OverMorphism.ext (congrArg PolarizedFamily.Hom.baseMap h))
  subst hg
  have hl : ampleLineBundleIso hA hC ⟨g, fib, hfib⟩ = ampleLineBundleIso hA hC ⟨g, fib', hfib'⟩ :=
    eq_of_heq (PolarizedFamily.heq_lineBundleIso h)
  have hZr := Iso.trans_left_cancel _ hl
  have hqc := isQuasicoherentOnSite_modulePullback_ampleModelModule
    (ampleModelMap hA hC ⟨g, fib, hfib⟩)
  have hσ := Functor.mapIso_injective_of_injective _ _
    (bijective_representedZariski_map_space (ampleModel hA) ((Space.modulePullback B integerBase
      B.contains_integerBase (Space.representedSpaceMap B integerBase B.contains_integerBase
        (ampleModelMap hA hC ⟨g, fib, hfib⟩))).obj (ampleModelModule hC))
      (ampleModelModule hA) hqc).1 hZr
  have he := Iso.trans_left_cancel _ hσ
  have : (Space.modulePullback B integerBase B.contains_integerBase
      (ampleModelSpaceIso hA).hom).Faithful :=
    (hc.modulePullbackEquivalence (ampleModelSpaceIso hA)).faithful_functor
  have hiso := Functor.mapIso_injective _ he
  have h2 := congrArg Iso.hom hiso
  simp only [picardFibreIso_hom] at h2
  subst h2
  rfl

variable (hc X₀) in
/-- **The functor from the relatively ample locus of the Picard stack to the polarized families
over `X₀` is faithful.** -/
instance faithful_amplePolarizedFunctor : (amplePolarizedFunctor X₀ hc).Faithful where
  map_injective {A C} f g h := by
    apply ObjectProperty.hom_ext
    exact amplePolarizedHom_injective (congrArg CommaMorphism.left h)

/-! ### Fullness -/

/-- The image of the isomorphism reflected by `CategoryTheory.isoOfBijectiveMap` is the given
isomorphism. -/
theorem mapIso_isoOfBijectiveMap {C₀ D₀ : Type*} [Category* C₀] [Category* D₀] (G : C₀ ⥤ D₀)
    {X Y : C₀} (hXY : Function.Bijective fun x : X ⟶ Y => G.map x)
    (hYX : Function.Bijective fun x : Y ⟶ X => G.map x)
    (hXX : Function.Injective fun x : X ⟶ X => G.map x)
    (hYY : Function.Injective fun x : Y ⟶ Y => G.map x) (e : G.obj X ≅ G.obj Y) :
    G.mapIso (isoOfBijectiveMap G hXY hYX hXX hYY e) = e :=
  Iso.ext (hXY.2 e.hom).choose_spec

/-- If `(G1 ⋙ G2).mapIso s = c.symm ≪≫ r`, then `c` followed by the image of `κ` composed with the
image of the preimage of `κ.symm ≪≫ s` is `r`. -/
theorem reflected_comparison_eq {𝒞 𝒟 𝒟₁ 𝒟₂ : Type*} [Category* 𝒞] [Category* 𝒟]
    [Category* 𝒟₁] [Category* 𝒟₂] (G1 : 𝒟 ⥤ 𝒟₁) (G2 : 𝒟₁ ⥤ 𝒞) (F : 𝒟₂ ⥤ 𝒟) (hFull : F.Full)
    (hFaithful : F.Faithful) {P : 𝒞} {X : 𝒟} {X' Y' : 𝒟₂} (c : P ≅ G2.obj (G1.obj X))
    (κ : X ≅ F.obj X') (s : X ≅ F.obj Y') (r : P ≅ G2.obj (G1.obj (F.obj Y')))
    (hz : (G1 ⋙ G2).mapIso s = c.symm ≪≫ r) :
    c ≪≫ G2.mapIso (G1.mapIso (κ ≪≫ F.mapIso (F.preimageIso (κ.symm ≪≫ s)))) = r := by
  have hpre : F.mapIso (F.preimageIso (κ.symm ≪≫ s)) = κ.symm ≪≫ s :=
    Iso.ext (F.map_preimage _)
  have hz' : G2.mapIso (G1.mapIso s) = c.symm ≪≫ r := hz
  rw [hpre, Iso.self_symm_id_assoc, hz', Iso.self_symm_id_assoc]

/-- Cancelling an isomorphism at the end of a composite. -/
theorem comp_hom_eq_of_eq_comp_inv {C₀ : Type*} [Category* C₀] {X Y Z W : C₀} {q : X ⟶ Z}
    (a : X ⟶ Y) (b : Y ⟶ W) (e : Z ≅ W) (h : q = a ≫ b ≫ e.inv) : q ≫ e.hom = a ≫ b := by
  rw [h, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

section Full

variable (b : amplePolarizedFamily hA ⟶ amplePolarizedFamily hC)
  (hw : (forgetPolarization B).map b ≫ ampleArrow hC = ampleArrow hA)

/-- The morphism of test schemes underlying a morphism of polarized families. -/
def ampleBaseOver : A.T.left ⟶ C.T.left :=
  Over.homMk b.baseMap (ObjectProperty.hom_ext _ (specULiftZIsTerminal.hom_ext _ _))

/-- The morphism of test schemes of a morphism of polarized families commutes with the
identifications of the test schemes with the schemes over the integers. -/
private theorem map_baseMap_comp_integerNormIso :
    (schemeSpaceFunctor B integerBase B.contains_integerBase).map
        ((schemeOverIntegers B).map b.baseMap) ≫
      (schemeSpaceFunctor B integerBase B.contains_integerBase).map (integerNormIso C.T.left).hom =
    (schemeSpaceFunctor B integerBase B.contains_integerBase).map (integerNormIso A.T.left).hom ≫
      (schemeSpaceFunctor B integerBase B.contains_integerBase).map (ampleBaseOver b) :=
  (Functor.map_comp _ _ _).symm.trans ((congrArg _ (Over.OverMorphism.ext
    ((Category.comp_id _).trans (Category.id_comp _).symm) :
      (schemeOverIntegers B).map b.baseMap ≫ (integerNormIso C.T.left).hom =
        (integerNormIso A.T.left).hom ≫ ampleBaseOver b)).trans (Functor.map_comp _ _ _))

include hw in
/-- The morphism of test schemes underlying a morphism of polarized families over `X₀` is a
morphism of test schemes over `V₀`. -/
theorem ampleBaseOver_comp :
    (schemeSpaceFunctor B integerBase B.contains_integerBase).map (ampleBaseOver b) ≫ C.T.hom =
      A.T.hom := by
  let F := schemeSpaceFunctor B integerBase B.contains_integerBase
  have hr : (schemeOverIntegers B).map b.baseMap ≫ ampleBaseMap C = ampleBaseMap A :=
    congrArg (fun k => k.hom.hom.right) hw
  have e1 := map_baseMap_comp_integerNormIso b
  have e2 : ∀ D : Space.PicardObject (properFlatPicardSituation X₀),
      F.map (ampleBaseMap D) = F.map (integerNormIso D.T.left).hom ≫ D.T.hom :=
    fun D => schemeSpaceMap_ampleBaseMap D
  have H : F.map (integerNormIso A.T.left).hom ≫ F.map (ampleBaseOver b) ≫ C.T.hom =
      F.map (integerNormIso A.T.left).hom ≫ A.T.hom :=
    (Category.assoc _ _ _).symm.trans ((congrArg (fun k => k ≫ C.T.hom) e1.symm).trans
      ((Category.assoc _ _ _).trans ((congrArg (fun k =>
        F.map ((schemeOverIntegers B).map b.baseMap) ≫ k) (e2 C).symm).trans
          ((F.map_comp _ _).symm.trans ((congrArg F.map hr).trans (e2 A))))))
  exact (cancel_epi _).1 H

/-- The morphism of test schemes over `V₀` underlying a morphism of polarized families over
`X₀`. -/
def ampleBase : A.T ⟶ C.T :=
  CostructuredArrow.homMk (ampleBaseOver b) (ampleBaseOver_comp b hw)

include hw in
/-- The morphism of scheme models underlying a morphism of polarized families over `X₀` is the
morphism of scheme models of its morphism of test schemes: maps into `X_T` are determined by their
two projections. -/
theorem totalMapOverIntegers_eq_ampleModelBaseMap :
    PolarizedFamily.totalMapOverIntegers b = ampleModelBaseMap hA hC (ampleBase b hw) := by
  let F := schemeSpaceFunctor B integerBase B.contains_integerBase
  let t := PolarizedFamily.totalMapOverIntegers b
  let f₀ := (properFlatPicardSituation X₀).f
  have hl : F.map t ≫ ampleArrowLeft hC = ampleArrowLeft hA :=
    congrArg (fun k => k.hom.hom.left) hw
  have hcart : t ≫ ampleModelHom hC = ampleModelHom hA ≫ (schemeOverIntegers B).map b.baseMap :=
    (PolarizedFamily.isPullback_totalMapOverIntegers b).w
  have hq : ∀ D (hD : Space.picardAmple hc (properFlatPicardSituation X₀) D),
      F.map (ampleModelHom hD) ≫ F.map (integerNormIso D.T.left).hom =
        (ampleModelSpaceIso hD).hom ≫ Space.baseChangeInclusion f₀ D.T := fun D hD =>
    comp_hom_eq_of_eq_comp_inv _ _ (F.mapIso (integerNormIso D.T.left))
      (schemeSpaceMap_ampleModelHom hD)
  have hsq : F.map t ≫ (ampleModelSpaceIso hC).hom =
      (ampleModelSpaceIso hA).hom ≫ Space.baseChangeMap f₀ (ampleBase b hw) := by
    refine Space.baseChange_hom_ext f₀ ?_ ?_
    · exact (Category.assoc _ _ _).trans (hl.trans ((congrArg (fun k =>
        (ampleModelSpaceIso hA).hom ≫ k) (Space.baseChangeMap_comp_projection f₀
          (ampleBase b hw))).symm.trans (Category.assoc _ _ _).symm))
    · have e1 := map_baseMap_comp_integerNormIso b
      have hcartF : F.map t ≫ F.map (ampleModelHom hC) =
          F.map (ampleModelHom hA) ≫ F.map ((schemeOverIntegers B).map b.baseMap) :=
        (F.map_comp _ _).symm.trans ((congrArg F.map hcart).trans (F.map_comp _ _))
      exact (Category.assoc _ _ _).trans ((congrArg (fun k => F.map t ≫ k) (hq C hC).symm).trans
        ((Category.assoc _ _ _).symm.trans ((congrArg (fun k => k ≫
          F.map (integerNormIso C.T.left).hom) hcartF).trans ((Category.assoc _ _ _).trans
            ((congrArg (fun k => F.map (ampleModelHom hA) ≫ k) e1).trans
              ((Category.assoc _ _ _).symm.trans ((congrArg (fun k => k ≫
                F.map (ampleBaseOver b)) (hq A hA)).trans ((Category.assoc _ _ _).trans
                  ((congrArg (fun k => (ampleModelSpaceIso hA).hom ≫ k)
                    (Space.baseChangeMap_comp_inclusion f₀ (ampleBase b hw)).symm).trans
                      (Category.assoc _ _ _).symm)))))))))
  apply yoneda.map_injective
  have h2 : F.map t = ((ampleModelSpaceIso hA).hom ≫ Space.baseChangeMap f₀ (ampleBase b hw)) ≫
      (ampleModelSpaceIso hC).inv := (Iso.eq_comp_inv _).2 hsq
  exact (congrArg (fun k => k.hom) h2).trans (yoneda.map_preimage _).symm

include hw in
/-- The morphism of total spaces of a morphism of polarized families over `X₀` is the morphism of
scheme models of its morphism of test schemes. -/
theorem totalMap_eq_ampleModelBaseMap :
    b.totalMap = SmallEtale.schemeHom (associatedBigEtaleSite B)
      (ampleModelBaseMap hA hC (ampleBase b hw)).left :=
  congrArg (fun k : ampleModel hA ⟶ ampleModel hC =>
    SmallEtale.schemeHom (associatedBigEtaleSite B) k.left)
    (totalMapOverIntegers_eq_ampleModelBaseMap b hw)

/-- The comparison of polarizations of a morphism of polarized families over `X₀`, read on the
represented algebraic spaces through the reading of modules on schemes. -/
def ampleZariskiComparison :
    Space.representedZariskiModule B integerBase B.contains_integerBase (ampleModel hA)
        ((Space.modulePullback B integerBase B.contains_integerBase
          (Space.representedSpaceMap B integerBase B.contains_integerBase
            (ampleModelBaseMap hA hC (ampleBase b hw)))).obj (ampleModelModule hC)) ≅
      Space.representedZariskiModule B integerBase B.contains_integerBase (ampleModel hA)
        (ampleModelModule hA) :=
  (Space.representedZariskiModulePullbackIso B integerBase B.contains_integerBase
      (ampleModelBaseMap hA hC (ampleBase b hw))
      (Space.relativelyRepresentable_yoneda_map B integerBase B.contains_integerBase _)
      (ampleModelModule hC) (isQuasicoherentOnSite_ampleModelModule hC)).symm ≪≫
    eqToIso (congrArg (fun k => (Scheme.Modules.pullback k).obj (ampleModelLineBundle hC))
      (totalMap_eq_ampleModelBaseMap b hw).symm) ≪≫ b.lineBundleIso

/-- The comparison of the modules on the represented algebraic spaces of a morphism of polarized
families over `X₀`, reflected from the comparison of polarizations
(`AlgebraicGeometry.Space.QuasiCoherentDescent.bijective_representedZariski_map`). -/
def ampleSpaceComparison :
    (Space.modulePullback B integerBase B.contains_integerBase
        (Space.representedSpaceMap B integerBase B.contains_integerBase
          (ampleModelBaseMap hA hC (ampleBase b hw)))).obj (ampleModelModule hC) ≅
      ampleModelModule hA :=
  have hqc := Space.isQuasicoherentOnSite_modulePullback_representedSpaceMap B integerBase
    B.contains_integerBase (ampleModelBaseMap hA hC (ampleBase b hw))
    (Space.relativelyRepresentable_yoneda_map B integerBase B.contains_integerBase _) _
    (isQuasicoherentOnSite_ampleModelModule hC)
  isoOfBijectiveMap
    ((Space.representedSmallEtaleModuleEquivalence B integerBase B.contains_integerBase
      (ampleModel hA)).inverse ⋙ SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B integerBase B.contains_integerBase).obj (ampleModel hA))
        (ampleModel hA).left.property)
    (bijective_representedZariski_map_space _ _ _ hqc)
    (bijective_representedZariski_map_space _ _ _ (isQuasicoherentOnSite_ampleModelModule hA))
    (bijective_representedZariski_map_space _ _ _ hqc).1
    (bijective_representedZariski_map_space _ _ _
      (isQuasicoherentOnSite_ampleModelModule hA)).1
    (ampleZariskiComparison b hw)

omit b hw in
/-- The inverse image along an isomorphism of algebraic spaces is full. -/
theorem full_modulePullback_ampleModelSpaceIso :
    (Space.modulePullback B integerBase B.contains_integerBase (ampleModelSpaceIso hA).hom).Full :=
  (hc.modulePullbackEquivalence (ampleModelSpaceIso hA)).full_functor

omit b hw in
/-- The inverse image along an isomorphism of algebraic spaces is faithful. -/
theorem faithful_modulePullback_ampleModelSpaceIso :
    (Space.modulePullback B integerBase B.contains_integerBase
      (ampleModelSpaceIso hA).hom).Faithful :=
  (hc.modulePullbackEquivalence (ampleModelSpaceIso hA)).faithful_functor

/-- The comparison of modules of the morphism of the Picard stack reflected from a morphism of
polarized families over `X₀`. -/
def ampleFibreOf :
    (Space.modulePullback B integerBase B.contains_integerBase
        (Space.baseChangeMap (properFlatPicardSituation X₀).f (ampleBase b hw))).obj
        C.lineBundle ≅ A.lineBundle :=
  haveI := full_modulePullback_ampleModelSpaceIso (hc := hc) (hA := hA)
  haveI := faithful_modulePullback_ampleModelSpaceIso (hc := hc) (hA := hA)
  (Space.modulePullback B integerBase B.contains_integerBase
      (ampleModelSpaceIso hA).hom).preimageIso
    ((Space.QuasiCoherentDescent.canonicalComparison _ _ _ _
      (ampleModelBaseMap_comp_ampleModelSpaceIso (ampleBase b hw)) C.lineBundle).symm ≪≫
      ampleSpaceComparison b hw)

/-- **The morphism of the Picard stack reflected from a morphism of polarized families over
`X₀`.** -/
def ampleHomOf : Space.PicardHom A C where
  base := ampleBase b hw
  fibre := (ampleFibreOf b hw).hom
  isIso_fibre := inferInstance

/-- The reflected morphism of the Picard stack is carried back to the given morphism of polarized
families. -/
theorem amplePolarizedHom_ampleHomOf : amplePolarizedHom hA hC (ampleHomOf b hw) = b := by
  refine PolarizedFamily.Hom.ext rfl (totalMap_eq_ampleModelBaseMap b hw).symm ?_
  have := full_modulePullback_ampleModelSpaceIso (hc := hc) (hA := hA)
  have := faithful_modulePullback_ampleModelSpaceIso (hc := hc) (hA := hA)
  have hqc := isQuasicoherentOnSite_modulePullback_ampleModelModule
    (ampleModelBaseMap hA hC (ampleBase b hw))
  have hz := mapIso_isoOfBijectiveMap
    ((Space.representedSmallEtaleModuleEquivalence B integerBase B.contains_integerBase
      (ampleModel hA)).inverse ⋙ SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B integerBase B.contains_integerBase).obj (ampleModel hA))
        (ampleModel hA).left.property)
    (bijective_representedZariski_map_space _ _ _ hqc)
    (bijective_representedZariski_map_space _ _ _ (isQuasicoherentOnSite_ampleModelModule hA))
    (bijective_representedZariski_map_space _ _ _ hqc).1
    (bijective_representedZariski_map_space _ _ _
      (isQuasicoherentOnSite_ampleModelModule hA)).1
    (ampleZariskiComparison b hw)
  have key := reflected_comparison_eq
    (Space.representedSmallEtaleModuleEquivalence B integerBase B.contains_integerBase
      (ampleModel hA)).inverse
    (SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B integerBase B.contains_integerBase).obj (ampleModel hA))
        (ampleModel hA).left.property)
    (Space.modulePullback B integerBase B.contains_integerBase (ampleModelSpaceIso hA).hom)
    (full_modulePullback_ampleModelSpaceIso (hc := hc) (hA := hA))
    (faithful_modulePullback_ampleModelSpaceIso (hc := hc) (hA := hA))
    _ (Space.QuasiCoherentDescent.canonicalComparison _ _ _ _
      (ampleModelBaseMap_comp_ampleModelSpaceIso (ampleBase b hw)) C.lineBundle) _ _ hz
  have hfib : picardFibreIso (ampleHomOf b hw) = ampleFibreOf b hw := Iso.ext rfl
  change ampleLineBundleIso hA hC (ampleHomOf b hw) ≍ b.lineBundleIso
  rw [ampleLineBundleIso, ampleModuleComparison, hfib]
  exact (heq_of_eq key).trans (PolarizedFamily.eqToIso_trans_heq _ _)

end Full

variable (hc X₀) in
/-- **The functor from the relatively ample locus of the Picard stack to the polarized families
over `X₀` is full.** -/
instance full_amplePolarizedFunctor : (amplePolarizedFunctor X₀ hc).Full where
  map_surjective φ :=
    ⟨ObjectProperty.homMk (ampleHomOf φ.left (CostructuredArrow.w φ)),
      CostructuredArrow.hom_ext _ _ (amplePolarizedHom_ampleHomOf φ.left (CostructuredArrow.w φ))⟩

end AlgebraicGeometry

end
