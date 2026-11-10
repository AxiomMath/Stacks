module

public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedPicardMorphism
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedStackUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.CanonicalPaste
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.RepresentedZariskiCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.RepresentedZariskiTransitionSquare

/-!
# The functor from the relatively ample locus of a Picard stack to the polarized families

Fix an object `X₀ ⟶ V₀` of `Spaces'_{fp, flat, proper}` over the big fppf site of `Spec(ℤ)`.
To every relatively ample object `(T, L)` of `Picardstack_{X₀/V₀}` is attached a polarized family
over `X₀` (`AlgebraicGeometry.amplePolarizedFamily`), and to every morphism of such objects a
morphism of polarized families over `X₀` (`AlgebraicGeometry.amplePolarizedHom`). This file shows
that this is a functor: the comparisons of polarizations compose, by the composition law of the
reading of modules on represented algebraic spaces as modules on schemes
(`AlgebraicGeometry.Space.representedZariskiModulePullbackIso_comp_iso`) and the pasting law of
canonical comparisons of inverse images
(`AlgebraicGeometry.Space.QuasiCoherentDescent.canonicalComparison_paste`).

## Main definitions

* `AlgebraicGeometry.amplePolarizedFunctor`: the functor from the relatively ample locus of
  `Picardstack_{X₀/V₀}` to the polarized families over `X₀`.

## Main results

* `AlgebraicGeometry.ampleModelMap_comp`: the morphisms of scheme models compose.
* `AlgebraicGeometry.ampleModuleComparison_comp`: the comparisons on the represented algebraic
  spaces compose.
* `AlgebraicGeometry.ampleLineBundleIso_comp`: the comparisons on the schemes compose.
* `AlgebraicGeometry.amplePolarizedHom_comp`: the morphisms of polarized families compose.

## References

* [Stacks Project, Tag 0D41](https://stacks.math.columbia.edu/tag/0D41)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {B : BigFppfSite.{u}} {X₀ : CartesianProperFlatSpaces B integerBase B.contains_integerBase}
  {hc : Space.ModulePushforwardCoherence B integerBase B.contains_integerBase}

variable {A C D : Space.PicardObject (properFlatPicardSituation X₀)}
  {hA : Space.picardAmple hc (properFlatPicardSituation X₀) A}
  {hC : Space.picardAmple hc (properFlatPicardSituation X₀) C}
  {hD : Space.picardAmple hc (properFlatPicardSituation X₀) D}

/-! ### Composites of comparisons, as isomorphisms -/

/-- The composite comparison `CategoryTheory.Functor.fibreComp` of two isomorphisms, as an
isomorphism. -/
theorem asIso_fibreComp {C₀ C₁ C₂ : Type*} [Category* C₀] [Category* C₁] [Category* C₂]
    {La : C₁ ⥤ C₀} {Lb : C₂ ⥤ C₁} {Lab : C₂ ⥤ C₀} (τ : Lab ≅ Lb ⋙ La) {M : C₀} {M' : C₁}
    {M'' : C₂} (a : La.obj M' ⟶ M) (b : Lb.obj M'' ⟶ M') [IsIso a] [IsIso b]
    (e : Lab.obj M'' ≅ M) (he : e.hom = Functor.fibreComp τ a b) :
    e = τ.app M'' ≪≫ La.mapIso (asIso b) ≪≫ asIso a :=
  Iso.ext he

/-- If `e ≪≫ f = g`, then `f` is `e.symm ≪≫ g`. -/
private theorem eq_symm_trans_of_trans_eq {C₀ : Type*} [Category* C₀] {X Y Z : C₀} {e : X ≅ Y}
    {f : Y ≅ Z} {g : X ≅ Z} (h : e ≪≫ f = g) : f = e.symm ≪≫ g := by
  rw [← h, Iso.symm_self_id_assoc]

/-- A comparison `c` of two pseudofunctors which satisfies a congruence law, a composition law and
a naturality law carries a cocycle of transitions to a cocycle of transitions. -/
theorem Iso.transported_cocycle {𝒞 𝒞' 𝒟 𝒟' 𝒟₁ 𝒟₁' : Type*} [Category* 𝒞] [Category* 𝒞']
    [Category* 𝒟] [Category* 𝒟'] [Category* 𝒟₁] [Category* 𝒟₁']
    (G1 : 𝒟 ⥤ 𝒟₁) (G2 : 𝒟₁ ⥤ 𝒞) (G1' : 𝒟' ⥤ 𝒟₁') (G2' : 𝒟₁' ⥤ 𝒞') (pb : 𝒞' ⥤ 𝒞)
    (aPull : 𝒟' ⥤ 𝒟) {Fmn Fmn' FA : 𝒟} {aF FC : 𝒟'} {X1 X2 : 𝒞} {Y1 : 𝒞'}
    (c_mn : X1 ≅ G2.obj (G1.obj Fmn)) (c_mm : X2 ≅ G2.obj (G1.obj Fmn')) (E : Fmn' ≅ Fmn)
    (E' : X2 ≅ X1) (hcongr : c_mm ≪≫ G2.mapIso (G1.mapIso E) = E' ≪≫ c_mn)
    (s_mn : Fmn ≅ FA) (R : aPull.obj aF ≅ Fmn') (s_n : aF ≅ FC) (s_m : aPull.obj FC ≅ FA)
    (hσ : R.symm ≪≫ aPull.mapIso s_n ≪≫ s_m = E ≪≫ s_mn)
    (c_n : Y1 ≅ G2'.obj (G1'.obj aF)) (c_m' : pb.obj (G2'.obj (G1'.obj aF)) ≅
      G2.obj (G1.obj (aPull.obj aF))) (P : pb.obj Y1 ≅ X2)
    (hcomp : pb.mapIso c_n ≪≫ c_m' ≪≫ G2.mapIso (G1.mapIso R) = P ≪≫ c_mm)
    (c_m : pb.obj (G2'.obj (G1'.obj FC)) ≅ G2.obj (G1.obj (aPull.obj FC)))
    (hnat : pb.mapIso (G2'.mapIso (G1'.mapIso s_n)) ≪≫ c_m =
      c_m' ≪≫ G2.mapIso (G1.mapIso (aPull.mapIso s_n))) :
    c_mn ≪≫ G2.mapIso (G1.mapIso s_mn) =
      E'.symm ≪≫ P.symm ≪≫ pb.mapIso (c_n ≪≫ G2'.mapIso (G1'.mapIso s_n)) ≪≫
        (c_m ≪≫ G2.mapIso (G1.mapIso s_m)) := by
  rw [eq_symm_trans_of_trans_eq hcongr.symm, eq_symm_trans_of_trans_eq hcomp.symm,
    eq_symm_trans_of_trans_eq hσ.symm]
  simp only [Functor.mapIso_trans, Functor.mapIso_symm, Iso.trans_assoc,
    Iso.self_symm_id_assoc]
  rw [← Iso.trans_assoc c_m' _ _, ← hnat, Iso.trans_assoc]

/-- An inverse transport along an equality of objects followed by an isomorphism is
heterogeneously that isomorphism. -/
theorem eqToIso_symm_trans_heq {C₀ : Type*} [Category* C₀] {X X' Y : C₀} (h : X = X')
    (e : X ≅ Y) : (eqToIso h).symm ≪≫ e ≍ e := by
  cases h
  simp only [eqToIso_refl, Iso.refl_symm, Iso.refl_trans]
  rfl

/-! ### The contraction of inverse images along represented morphisms -/

open Space.QuasiCoherentDescent in
/-- The contraction of the inverse images along two composable represented morphisms, read
backwards at a module, is the comparison of the inverse image along the composite with the
iterated inverse image. -/
theorem representedModulePullbackCompIso_app_symm {S : Scheme.{u}} {hS : B.Contains S}
    {T'' T' T : BigFppfOver B S hS} (h : T'' ⟶ T') (g : T' ⟶ T)
    (F : Space.Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)) :
    ((Space.representedModulePullbackCompIso B S hS h g).app F).symm =
      pullbackComparison B S hS (Space.representedSpaceMap B S hS h)
        (Space.representedSpaceMap B S hS g) (Space.representedSpaceMap B S hS (h ≫ g))
        (Space.representedSpaceMap_comp B S hS h g) F := by
  rw [pullbackComparison_eq_eqToIso, pullbackComparison_rfl]
  ext
  simp [Space.representedModulePullbackCompIso, eqToHom_app]

/-! ### The morphisms of scheme models compose -/

/-- The morphism of scheme models of a composite is the composite of the morphisms of scheme
models. -/
theorem ampleModelMap_comp (m : Space.PicardHom A C) (n : Space.PicardHom C D) :
    ampleModelMap hA hD (Space.PicardHom.comp m n) =
      ampleModelMap hA hC m ≫ ampleModelMap hC hD n := by
  apply yoneda.map_injective
  have h1 : schemeSpaceMap (ampleModelMap hA hD (Space.PicardHom.comp m n)) =
      schemeSpaceMap (ampleModelMap hA hC m) ≫ schemeSpaceMap (ampleModelMap hC hD n) := by
    rw [schemeSpaceMap_ampleModelMap, schemeSpaceMap_ampleModelMap,
      schemeSpaceMap_ampleModelMap]
    change _ ≫ Space.baseChangeMap _ (m.base ≫ n.base) ≫ _ = _
    rw [Space.baseChangeMap_comp]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact (congrArg (fun k => k.hom) h1).trans (yoneda.map_comp _ _).symm

/-! ### The comparisons on the represented algebraic spaces compose -/

open Space.QuasiCoherentDescent in
/-- **The comparisons of polarizations on the represented algebraic spaces compose.** For
morphisms `m : A ⟶ C` and `n : C ⟶ D` of the Picard stack between relatively ample objects, the
comparison of the composite is, up to the identification of the morphism of scheme models of the
composite with the composite of the morphisms of scheme models, the comparison of `n` pulled back
along the morphism of scheme models of `m`, followed by the comparison of `m`. -/
theorem ampleModuleComparison_comp (m : Space.PicardHom A C) (n : Space.PicardHom C D) :
    ((Space.representedModulePullbackCompIso B integerBase B.contains_integerBase
        (ampleModelMap hA hC m) (ampleModelMap hC hD n)).app (ampleModelModule hD)).symm ≪≫
      (Space.modulePullback B integerBase B.contains_integerBase
        (Space.representedSpaceMap B integerBase B.contains_integerBase
          (ampleModelMap hA hC m))).mapIso (ampleModuleComparison hC hD n) ≪≫
      ampleModuleComparison hA hC m =
    eqToIso (congrArg (fun k => (Space.modulePullback B integerBase B.contains_integerBase
        (Space.representedSpaceMap B integerBase B.contains_integerBase k)).obj
          (ampleModelModule hD)) (ampleModelMap_comp m n).symm) ≪≫
      ampleModuleComparison hA hD (Space.PicardHom.comp m n) := by
  have hz : Space.baseChangeMap (properFlatPicardSituation X₀).f m.base ≫
      Space.baseChangeMap (properFlatPicardSituation X₀).f n.base =
      Space.baseChangeMap (properFlatPicardSituation X₀).f (Space.PicardHom.comp m n).base :=
    (Space.baseChangeMap_comp (properFlatPicardSituation X₀).f m.base n.base).symm
  have hfib : picardFibreIso (Space.PicardHom.comp m n) =
      pullbackComparison B integerBase B.contains_integerBase
          (Space.baseChangeMap (properFlatPicardSituation X₀).f m.base)
          (Space.baseChangeMap (properFlatPicardSituation X₀).f n.base) _ hz D.lineBundle ≪≫
        (Space.modulePullback B integerBase B.contains_integerBase
          (Space.baseChangeMap (properFlatPicardSituation X₀).f m.base)).mapIso
            (picardFibreIso n) ≪≫ picardFibreIso m := by
    have h0 := asIso_fibreComp
      (Space.baseChangeCompComparison (properFlatPicardSituation X₀).f m.base n.base)
      m.fibre n.fibre (picardFibreIso (Space.PicardHom.comp m n)) rfl
    exact h0.trans (congrArg (fun i => i ≪≫ _) (modulePullbackTriangle_app hz D.lineBundle))
  rw [representedModulePullbackCompIso_app_symm]
  refine (canonicalComparison_cocycle _ _
    (Space.representedSpaceMap_comp B integerBase B.contains_integerBase _ _)
    (congrArg (Space.representedSpaceMap B integerBase B.contains_integerBase)
      (ampleModelMap_comp m n).symm) _ _ _ _ _ hz
    (ampleModelMap_comp_ampleModelSpaceIso m) (ampleModelMap_comp_ampleModelSpaceIso n)
    (ampleModelMap_comp_ampleModelSpaceIso (Space.PicardHom.comp m n)) D.lineBundle
    (picardFibreIso n) (picardFibreIso m)).trans ?_
  exact congrArg (fun i => eqToIso _ ≪≫ canonicalComparison _ _ _ _
    (ampleModelMap_comp_ampleModelSpaceIso (Space.PicardHom.comp m n)) D.lineBundle ≪≫
      (Space.modulePullback B integerBase B.contains_integerBase
        (ampleModelSpaceIso hA).hom).mapIso i) hfib.symm

/-! ### The comparisons on the schemes compose -/

/-- **The comparisons of polarizations on the scheme models compose.** For morphisms
`m : A ⟶ C` and `n : C ⟶ D` of the Picard stack between relatively ample objects, the comparison
of polarizations of the composite is, up to the identification of the morphism of scheme models
of the composite with the composite of the morphisms of scheme models, the comparison of `n`
pulled back along the morphism of scheme models of `m`, followed by the comparison of `m`. -/
theorem ampleLineBundleIso_comp (m : Space.PicardHom A C) (n : Space.PicardHom C D) :
    ampleLineBundleIso hA hD (Space.PicardHom.comp m n) =
      (eqToIso (congrArg (fun k : ampleModel hA ⟶ ampleModel hD =>
          (Scheme.Modules.pullback (SmallEtale.schemeHom (associatedBigEtaleSite B) k.left)).obj
            (ampleModelLineBundle hD)) (ampleModelMap_comp m n).symm)).symm ≪≫
        ((Scheme.Modules.pullbackComp
            (SmallEtale.schemeHom (associatedBigEtaleSite B) (ampleModelMap hA hC m).left)
            (SmallEtale.schemeHom (associatedBigEtaleSite B)
              (ampleModelMap hC hD n).left)).app (ampleModelLineBundle hD)).symm ≪≫
        (Scheme.Modules.pullback (SmallEtale.schemeHom (associatedBigEtaleSite B)
          (ampleModelMap hA hC m).left)).mapIso (ampleLineBundleIso hC hD n) ≪≫
        ampleLineBundleIso hA hC m := by
  have hcongr := Space.representedZariskiModulePullbackIso_congr B integerBase
    B.contains_integerBase (ampleModelModule hD) (isQuasicoherentOnSite_ampleModelModule hD)
    (ampleModelMap_comp (hA := hA) (hC := hC) (hD := hD) m n).symm
  have hcomp := Space.representedZariskiModulePullbackIso_comp_iso B integerBase
    B.contains_integerBase (ampleModelMap hA hC m) (ampleModelMap hC hD n)
    (Space.relativelyRepresentable_yoneda_map B integerBase B.contains_integerBase _)
    (Space.relativelyRepresentable_yoneda_map B integerBase B.contains_integerBase _)
    (Space.relativelyRepresentable_yoneda_map B integerBase B.contains_integerBase _)
    (ampleModelModule hD) (isQuasicoherentOnSite_ampleModelModule hD)
  have hnat := Space.representedZariskiModulePullbackIso_naturality_iso B integerBase
    B.contains_integerBase (ampleModelMap hA hC m)
    (Space.relativelyRepresentable_yoneda_map B integerBase B.contains_integerBase _)
    (Space.isQuasicoherentOnSite_modulePullback_representedSpaceMap B integerBase
      B.contains_integerBase _
      (Space.relativelyRepresentable_yoneda_map B integerBase B.contains_integerBase _)
      _ (isQuasicoherentOnSite_ampleModelModule hD))
    (isQuasicoherentOnSite_ampleModelModule hC) (ampleModuleComparison hC hD n)
  have hσ := ampleModuleComparison_comp (hA := hA) (hC := hC) (hD := hD) m n
  have key := Iso.transported_cocycle
    (Space.representedSmallEtaleModuleEquivalence B integerBase B.contains_integerBase
      (ampleModel hA)).inverse
    (SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B integerBase B.contains_integerBase).obj (ampleModel hA))
      (ampleModel hA).left.property)
    (Space.representedSmallEtaleModuleEquivalence B integerBase B.contains_integerBase
      (ampleModel hC)).inverse
    (SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B integerBase B.contains_integerBase).obj (ampleModel hC))
      (ampleModel hC).left.property)
    (Scheme.Modules.pullback (SmallEtale.schemeHom (associatedBigEtaleSite B)
      (ampleModelMap hA hC m).left))
    (Space.modulePullback B integerBase B.contains_integerBase
      (Space.representedSpaceMap B integerBase B.contains_integerBase (ampleModelMap hA hC m)))
    _ _ _ _ hcongr _ _ _ _ hσ _ _ _ hcomp _ hnat
  rw [ampleLineBundleIso, ampleLineBundleIso, ampleLineBundleIso]
  exact key

/-! ### The morphisms of polarized families compose -/

/-- **The morphisms of polarized families of the relatively ample locus compose.** -/
theorem amplePolarizedHom_comp (m : Space.PicardHom A C) (n : Space.PicardHom C D) :
    amplePolarizedHom hA hD (Space.PicardHom.comp m n) =
      amplePolarizedHom hA hC m ≫ amplePolarizedHom hC hD n := by
  refine PolarizedFamily.Hom.ext rfl ?_ ?_
  · exact (congrArg (fun k : ampleModel hA ⟶ ampleModel hD =>
      SmallEtale.schemeHom (associatedBigEtaleSite B) k.left) (ampleModelMap_comp m n)).trans
      (B.inclusion.map_comp _ _)
  · change ampleLineBundleIso hA hD (Space.PicardHom.comp m n) ≍
      ((Scheme.Modules.pullbackComp
          (SmallEtale.schemeHom (associatedBigEtaleSite B) (ampleModelMap hA hC m).left)
          (SmallEtale.schemeHom (associatedBigEtaleSite B)
            (ampleModelMap hC hD n).left)).symm.app (ampleModelLineBundle hD) ≪≫
        (Scheme.Modules.pullback (SmallEtale.schemeHom (associatedBigEtaleSite B)
          (ampleModelMap hA hC m).left)).mapIso (ampleLineBundleIso hC hD n) ≪≫
        ampleLineBundleIso hA hC m)
    rw [ampleLineBundleIso_comp]
    exact eqToIso_symm_trans_heq _ _

/-- **The morphism of polarized families of an identity is the identity.** -/
theorem amplePolarizedHom_id :
    amplePolarizedHom hA hA (Space.PicardHom.id hc A) = 𝟙 (amplePolarizedFamily hA) := by
  set e := amplePolarizedHom hA hA (Space.PicardHom.id hc A) with he
  have hee : e ≫ e = e := by
    rw [he, ← amplePolarizedHom_comp, Space.PicardHom.id_comp hc]
  have hbase : IsIso ((polarizedProjection B).map e) :=
    (inferInstance : IsIso (𝟙 A.T.left.left))
  have : (polarizedProjection B).IsStronglyCartesian ((polarizedProjection B).map e) e :=
    Functor.IsFiberedInGroupoids.isStronglyCartesian_homLift
      polarizedProjection_isFiberedInGroupoids_unconditional _ e
  have : IsIso e := Functor.IsStronglyCartesian.isIso_of_base_isIso (polarizedProjection B)
    ((polarizedProjection B).map e) e
  exact (cancel_epi e).1 (hee.trans (Category.comp_id e).symm)

/-! ### The functor -/

variable (hc X₀) in
/-- **The polarized families of the relatively ample locus of `Picardstack_{X₀/V₀}`, as
polarized families over `X₀`.** An object `(T, L)` with `L` ample on `X_T/T` is sent to the
polarized family `(Z ⟶ T, L|_Z)` of its scheme model, with the cartesian morphism from
`Z ⟶ T` to `X₀ ⟶ V₀` in `Spaces'_{fp, flat, proper}`. -/
def amplePolarizedFunctor :
    (Space.picardAmple hc (properFlatPicardSituation X₀)).FullSubcategory ⥤
      CostructuredArrow (forgetPolarization B) X₀ where
  obj A := CostructuredArrow.mk (ampleArrow A.property)
  map {A C} f := CostructuredArrow.homMk (amplePolarizedHom A.property C.property f.hom)
    (amplePolarizedHom_comp_ampleArrow A.property C.property f.hom)
  map_id _ := CostructuredArrow.hom_ext _ _ amplePolarizedHom_id
  map_comp f g := CostructuredArrow.hom_ext _ _ (amplePolarizedHom_comp f.hom g.hom)

end AlgebraicGeometry

end
