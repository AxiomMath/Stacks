module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafCompletion
public import StacksFrontier.Homology.DerivedComplete.FlatAdicCompletionUniversal
public import StacksFrontier.CategoryTheory.Sites.WeaklyContractible
public import StacksFrontier.AlgebraicGeometry.ProEtale.DerivedCompleteConstantCoefficients
public import StacksFrontier.AlgebraicGeometry.ProEtale.Constructible.ConstantAdicReductions
public import StacksFrontier.AlgebraicGeometry.ProEtale.AdicCompletionCriterion

/-!
# Maps from the completed constant sheaf into a derived complete sheaf

Let `Λ` be a Noetherian ring and `I ⊂ Λ` an ideal. On a site, the completed constant sheaf
`Λ̲^∧ = lim (Λ/Iⁿ)̲` comes with the canonical map `Λ̲ ⟶ Λ̲^∧`. Maps out of `Λ̲^∧` into a sheaf of
`Λ`-modules `F` are the same as maps out of `Λ̲`, as soon as the sections of `F` over the members
of a covering family of objects are derived complete with respect to `I`. On the small pro-étale
site this applies to every derived complete sheaf of `Λ̲`-modules, the covering family being the
affine weakly contractible objects; so every global section of such a sheaf lies in the image of a
map `Λ̲^∧ ⟶ F`.

## Main results

* `Stacks.ConstantSheaf.completedConstantSectionsIsoAdicCompletion`: the sections of `Λ̲^∧` over
  an object are the `I`-adic completion of the sections of `Λ̲`, compatibly with the canonical
  maps (`sections_structureMap_comp_completedConstantSectionsIsoAdicCompletion_hom`).
* `Stacks.ConstantSheaf.bijective_comp_sections_structureMap`: on sections, maps out of
  `Λ̲^∧` into a derived complete module are maps out of `Λ̲`.
* `Stacks.ConstantSheaf.bijective_comp_completedConstantSheafStructureMap`: the same for maps of
  sheaves, when the target has derived complete sections over a covering family.
* `AlgebraicGeometry.ProEtale.isDerivedCompleteModule_toCoefficientModuleSheaf_obj`: the sections
  of a derived complete sheaf of `Λ̲`-modules on `X_proétale` over an affine weakly contractible
  object form a derived complete `Λ`-module.
* `AlgebraicGeometry.ProEtale.exists_completedConstantSheaf_hom_of_isDerivedComplete`: a global
  section of a derived complete sheaf of `Λ̲`-modules on `X_proétale` lies in the image of a map
  out of `Λ̲^∧`.

## References

* [Stacks Project, Tag 09BZ](https://stacks.math.columbia.edu/tag/09BZ)
* [Stacks Project, Tag 099M](https://stacks.math.columbia.edu/tag/099M)
* [Stacks Project, Tag 093M](https://stacks.math.columbia.edu/tag/093M)
* [Stacks Project, Tag 093L](https://stacks.math.columbia.edu/tag/093L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace Stacks.ConstantSheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable {R : Type w} [CommRing R] (I : Ideal R) [IsNoetherianRing R]
  [HasSheafify J (ModuleCat.{w} R)] [HasWeakSheafify J (Type w)]
  [J.PreservesSheafification (forget (ModuleCat.{w} R))]
  [J.HasSheafCompose (forget (ModuleCat.{w} R))]

/-- The sections of `R̲^∧` over `U`, as a limit cone over the `I`-adic quotient tower of the
sections of `R̲`: the projections are those of `R̲^∧` onto `(R/Iⁿ)̲`, read on sections and
composed with the inverse of `sectionsTowerComparison`. -/
def completedConstantSectionsCone (U : C) :
    Cone (quotientTower I ((constantSections.{u, v, w, w} J U).obj (ModuleCat.of R R))) :=
  (Cone.postcompose (inv (sectionsTowerComparison J I U))).obj
    (((sheafSections J (ModuleCat.{w} R)).obj (op U)).mapCone
      (limit.cone (adicQuotientSheafSystem J I)))

/-- `completedConstantSectionsCone` is a limit cone. -/
def completedConstantSectionsConeIsLimit (U : C) :
    IsLimit (completedConstantSectionsCone J I U) := by
  have hev : PreservesLimitsOfShape ℕᵒᵖ ((sheafSections J (ModuleCat.{w} R)).obj (op U)) :=
    preservesLimitsOfShape_of_natIso
      (sheafSectionsNatIsoEvaluation (J := J) (A := ModuleCat.{w} R) (X := U)).symm
  exact (IsLimit.postcomposeHomEquiv (asIso (inv (sectionsTowerComparison J I U))) _).symm
    (isLimitOfPreserves _ (limit.isLimit _))

/-- The sections of `R̲^∧` over `U` are the `I`-adic completion of the sections of `R̲`. -/
def completedConstantSectionsIsoAdicCompletion (U : C) :
    ((sheafSections J (ModuleCat.{w} R)).obj (op U)).obj (completedConstantSheaf J I) ≅
      ModuleCat.of R
        (AdicCompletion I ((constantSections.{u, v, w, w} J U).obj (ModuleCat.of R R))) :=
  (completedConstantSectionsConeIsLimit J I U).conePointUniqueUpToIso
    (adicCompletionIsLimit I _)

/-- The identification `completedConstantSectionsIsoAdicCompletion` carries the canonical map
`R̲ ⟶ R̲^∧`, read on sections, to the canonical map into the completion. -/
theorem sections_structureMap_comp_completedConstantSectionsIsoAdicCompletion_hom (U : C) :
    ((sheafSections J (ModuleCat.{w} R)).obj (op U)).map
        (completedConstantSheafStructureMap J I) ≫
      (completedConstantSectionsIsoAdicCompletion J I U).hom =
    ModuleCat.ofHom
      (AdicCompletion.of I ((constantSections.{u, v, w, w} J U).obj (ModuleCat.of R R))) := by
  have hcone : ∀ n : ℕᵒᵖ,
      ((sheafSections J (ModuleCat.{w} R)).obj (op U)).map
          (completedConstantSheafStructureMap J I) ≫ (completedConstantSectionsCone J I U).π.app n =
        ModuleCat.ofHom (I ^ n.unop • (⊤ : Submodule R
          ((constantSections.{u, v, w, w} J U).obj (ModuleCat.of R R)))).mkQ := by
    intro n
    show ((sheafSections J (ModuleCat.{w} R)).obj (op U)).map
        (completedConstantSheafStructureMap J I) ≫
      ((sheafSections J (ModuleCat.{w} R)).obj (op U)).map (completedConstantSheafπ J I n) ≫
        (inv (sectionsTowerComparison J I U)).app n = _
    rw [← Functor.map_comp_assoc]
    have h1 : completedConstantSheafStructureMap J I ≫ completedConstantSheafπ J I n =
        (constantSheaf J (ModuleCat.{w} R)).map (ModuleCat.ofHom (I ^ n.unop).mkQ) :=
      completedConstantSheafStructureMap_π J I n
    rw [h1, NatIso.isIso_inv_app]
    exact (IsIso.comp_inv_eq _).mpr
      (ModuleCat.hom_ext (LinearMap.ext fun a => (sectionsTowerComparison_app_mk J I U n a).symm))
  ext x n
  have key := congrArg (fun f => f.hom (((sheafSections J (ModuleCat.{w} R)).obj (op U)).map
      (completedConstantSheafStructureMap J I) |>.hom x))
    ((completedConstantSectionsConeIsLimit J I U).conePointUniqueUpToIso_hom_comp
      (adicCompletionIsLimit I _) (op n))
  have key2 := congrArg (fun f => f.hom x) (hcone (op n))
  exact key.trans key2

attribute [local instance] KoszulCompletion.derivedCountableProducts

/-- On the sections over `U`, precomposition with the canonical map `R̲ ⟶ R̲^∧` is a bijection
from the linear maps out of the sections of `R̲^∧` to the linear maps out of the sections of `R̲`,
whenever the target is derived complete with respect to `I`. -/
theorem bijective_comp_sections_structureMap (U : C) (M : Type w) [AddCommGroup M]
    [Module R M] (hM : IsDerivedCompleteModule I (ModuleCat.of R M)) :
    Function.Bijective (fun g : ((sheafSections J (ModuleCat.{w} R)).obj (op U)).obj
        (completedConstantSheaf J I) ⟶ ModuleCat.of R M =>
      ((sheafSections J (ModuleCat.{w} R)).obj (op U)).map
        (completedConstantSheafStructureMap J I) ≫ g) := by
  have : IsCoherentRing R := isCoherentRing_of_isNoetherianRing R
  let N := (constantSections.{u, v, w, w} J U).obj (ModuleCat.of R R)
  have hN : Module.Flat R N := flat_constantSections J (ModuleCat.of R R) U
  let e := completedConstantSectionsIsoAdicCompletion J I U
  have hU := AdicCompletionFlatTensor.bijective_comp_adicCompletionOf I N M hM
  have heq : (fun g : ((sheafSections J (ModuleCat.{w} R)).obj (op U)).obj
        (completedConstantSheaf J I) ⟶ ModuleCat.of R M =>
      ((sheafSections J (ModuleCat.{w} R)).obj (op U)).map
        (completedConstantSheafStructureMap J I) ≫ g) =
      (fun h : AdicCompletion I N →ₗ[R] M => ModuleCat.ofHom (h ∘ₗ AdicCompletion.of I N)) ∘
        (fun h => h.hom) ∘ (fun g => e.inv ≫ g) := by
    funext g
    simp only [Function.comp_apply]
    have hc := sections_structureMap_comp_completedConstantSectionsIsoAdicCompletion_hom J I U
    calc _ = (((sheafSections J (ModuleCat.{w} R)).obj (op U)).map
          (completedConstantSheafStructureMap J I) ≫ e.hom) ≫ e.inv ≫ g := by
            simp only [Category.assoc, Iso.hom_inv_id_assoc]
      _ = _ := by rw [hc]; rfl
  rw [heq]
  refine Function.Bijective.comp ?_ (Function.Bijective.comp ?_ ?_)
  · exact ⟨fun a b h => hU.1 (congrArg ModuleCat.Hom.hom h),
      fun f => ⟨(hU.2 f.hom).choose, ModuleCat.hom_ext (hU.2 f.hom).choose_spec⟩⟩
  · exact ⟨fun a b h => ModuleCat.hom_ext h, fun f => ⟨ModuleCat.ofHom f, rfl⟩⟩
  · exact ⟨fun a b h => by simpa using congrArg (fun g => e.hom ≫ g) h,
      fun f => ⟨e.hom ≫ f, by simp⟩⟩

/-- The sections of the completed constant sheaf `R̲^∧` over any object form a derived complete
`R`-module: they are an `I`-adic completion. -/
theorem isDerivedCompleteModule_completedConstantSheaf_sections (U : C) :
    IsDerivedCompleteModule I (ModuleCat.of R
      (((sheafSections J (ModuleCat.{w} R)).obj (op U)).obj (completedConstantSheaf J I))) := by
  let N := (constantSections.{u, v, w, w} J U).obj (ModuleCat.of R R)
  have hA : IsDerivedCompleteModule I (ModuleCat.of R (AdicCompletion I N)) :=
    (isDerivedCompleteModule_of_isAdicComplete_and_adicCompletion_surjective R I
      (AdicCompletion I N)).1 (AdicCompletion.isAdicComplete I.fg_of_isNoetherianRing)
  exact DerivedCompleteRecurrence.isDerivedComplete_of_iso
    ((DerivedCategory.singleFunctor (ModuleCat.{w} R) 0).mapIso
      (completedConstantSectionsIsoAdicCompletion J I U).symm) hA

omit [IsNoetherianRing R] [HasSheafify J (ModuleCat.{w} R)] [HasWeakSheafify J (Type w)]
  [J.PreservesSheafification (forget (ModuleCat.{w} R))]
  [J.HasSheafCompose (forget (ModuleCat.{w} R))] in
/-- The inclusion of a family of objects which covers every object of the site is cover dense. -/
theorem isCoverDense_ι_of_hasEnoughObjects (P : ObjectProperty C) (hP : J.HasEnoughObjects P) :
    P.ι.IsCoverDense J where
  is_cover U := by
    obtain ⟨ι, V, f, hf, hV⟩ := hP U
    refine J.superset_covering ?_ hf
    intro Y g hg
    obtain ⟨Z, h, _, ⟨i⟩, rfl⟩ := hg
    exact ⟨⟨⟨V i, hV i⟩, h, f i, rfl⟩⟩

/-- **Maps out of the completed constant sheaf.** Let `P` be a family of objects covering the site
such that the sections of a sheaf of `R`-modules `F` over each member of `P` are derived complete
with respect to `I`. Then every map `R̲ ⟶ F` factors uniquely through the canonical map
`R̲ ⟶ R̲^∧`. -/
theorem bijective_comp_completedConstantSheafStructureMap (P : ObjectProperty C)
    (hP : J.HasEnoughObjects P) (F : Sheaf J (ModuleCat.{w} R))
    (hF : ∀ W, P W → IsDerivedCompleteModule I (ModuleCat.of R (F.obj.obj (op W)))) :
    Function.Bijective (fun φ : completedConstantSheaf J I ⟶ F =>
      completedConstantSheafStructureMap J I ≫ φ) := by
  have : P.ι.IsCoverDense J := isCoverDense_ι_of_hasEnoughObjects J P hP
  let c := completedConstantSheafStructureMap J I
  have hbij : ∀ (U W : C), P W → Function.Bijective
      (fun g : (completedConstantSheaf J I).obj.obj (op U) ⟶ F.obj.obj (op W) =>
        c.hom.app (op U) ≫ g) := fun U W hW =>
    bijective_comp_sections_structureMap J I U (F.obj.obj (op W)) (hF W hW)
  have hext : ∀ {A : Sheaf J (ModuleCat.{w} R)} (φ₁ φ₂ : A ⟶ F),
      (∀ W : P.FullSubcategory, φ₁.hom.app (op W.obj) = φ₂.hom.app (op W.obj)) → φ₁ = φ₂ :=
    fun φ₁ φ₂ h => Sheaf.hom_ext
      ((Functor.IsCoverDense.restrictHomEquivHom (G := P.ι) (ℱ' := F)).symm.injective
        (NatTrans.ext (funext fun W => h W.unop)))
  refine ⟨fun φ₁ φ₂ h => hext φ₁ φ₂ fun W => (hbij W.obj W.obj W.property).1
    (congrArg (fun φ => φ.hom.app (op W.obj)) h), fun σ => ?_⟩
  choose g hg₀ using fun (W : P.FullSubcategory) =>
    (hbij W.obj W.obj W.property).2 (σ.hom.app (op W.obj))
  have hg : ∀ W : P.FullSubcategory, c.hom.app (op W.obj) ≫ g W = σ.hom.app (op W.obj) := hg₀
  let α : P.ι.op ⋙ (completedConstantSheaf J I).obj ⟶ P.ι.op ⋙ F.obj :=
    { app := fun W => g W.unop
      naturality := by
        intro W W' f
        apply (hbij W.unop.obj W'.unop.obj W'.unop.property).1
        have h1 : c.hom.app (op W.unop.obj) ≫ (completedConstantSheaf J I).obj.map
              (P.ι.map f.unop).op =
            ((constantSheaf J (ModuleCat.{w} R)).obj (ModuleCat.of R R)).obj.map
              (P.ι.map f.unop).op ≫ c.hom.app (op W'.unop.obj) :=
          (c.hom.naturality (P.ι.map f.unop).op).symm
        have h2 : ((constantSheaf J (ModuleCat.{w} R)).obj (ModuleCat.of R R)).obj.map
              (P.ι.map f.unop).op ≫ σ.hom.app (op W'.unop.obj) =
            σ.hom.app (op W.unop.obj) ≫ F.obj.map (P.ι.map f.unop).op :=
          σ.hom.naturality (P.ι.map f.unop).op
        show c.hom.app (op W.unop.obj) ≫ (completedConstantSheaf J I).obj.map
            (P.ι.map f.unop).op ≫ g W'.unop =
          c.hom.app (op W.unop.obj) ≫ g W.unop ≫ F.obj.map (P.ι.map f.unop).op
        rw [reassoc_of% h1, hg W'.unop, h2, ← hg W.unop, Category.assoc] }
  refine ⟨⟨Functor.IsCoverDense.sheafHom α⟩, hext _ _ fun W => ?_⟩
  exact (congrArg (c.hom.app _ ≫ ·) (congrArg (·.app (op W))
    (Functor.IsCoverDense.sheafHom_restrict_eq α))).trans (hg W)

end Stacks.ConstantSheaf

namespace AlgebraicGeometry.ProEtale

attribute [local instance] HasDerivedCategory.standard
  SheafOfModules.hasSheafify_commRingCat
  Stacks.hasSheafCompose_forget₂_commRingCat
  AlgebraicGeometry.ProEtale.hasSheafify_proetale_addCommGrpCat_succ
  AlgebraicGeometry.ProEtale.wEqualsLocallyBijective_proetale_addCommGrpCat_succ

variable (X : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ]

/-- The scalar of `λ : Λ` in the sections of the constant coefficient ring sheaf over `U`. -/
abbrev constantCoefficientScalar (U : X.ProEt) (l : Λ) :
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (constantCoefficientRingedSite.{u, u + 1, u} X Λ).O).obj.obj (op U) :=
  (constantCoefficientRingMap.{u, u + 1, u} X Λ).app (op U) (ULift.up l)

/-- In `toCoefficientModuleSheaf X Λ F`, the action of `l : Λ` on a section over `U` is the
action of the scalar `constantCoefficientScalar X Λ U l` in `F`. -/
theorem toCoefficientModuleSheaf_smul
    (F : RingedSite.Modules.{u + 1, u, u + 1} (constantCoefficientRingedSite.{u, u + 1, u} X Λ))
    (U : X.ProEt) (l : Λ) (x : F.val.obj (op U)) :
    (show F.val.obj (op U) from
      (l • (show ((toCoefficientModuleSheaf.{u, u + 1, u} X Λ).obj F).obj.obj (op U) from x))) =
      constantCoefficientScalar X Λ U l • x := by
  show ((Stacks.SheafOfModules.Tensor.ringSheaf
      (constantCoefficientRingedSite.{u, u + 1, u} X Λ).O).obj.map (terminal.from U).op
        (toCoefficientSections.{u, u + 1, u} X Λ l)) • x = _
  congr 1
  exact (congrArg (fun φ => CommRingCat.Hom.hom φ (ULift.up l))
    ((toSheafify (Scheme.ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj
      (CommRingCat.of (ULift.{u + 1} Λ)))).naturality (terminal.from U).op)).symm

variable (I : Ideal Λ)

/-- The scalar of an element of `I` is a section of the ideal sheaf `IΛ̲`. -/
theorem constantCoefficientScalar_mem (U : X.ProEt) {l : Λ} (hl : l ∈ I) :
    constantCoefficientScalar X Λ U l ∈
      (constantCoefficientIdealSheaf.{u, u + 1, u} X Λ I).toSubmodule.obj (op U) := by
  show constantCoefficientScalar X Λ U l ∈
    (_root_.SheafOfModules.kerIdeal (constantCoefficientRingReduction.{u, u + 1, u} X Λ I)).obj
      (op U)
  refine (SheafOfModules.mem_kerIdeal _ (op U) _).mpr ?_
  rw [RingHom.mem_ker]
  let π : ULift.{u + 1} Λ →+* ULift.{u + 1} (Λ ⧸ I) :=
    (ULift.ringEquiv.{u + 1, u + 1} (R := Λ ⧸ I)).symm.toRingHom.comp
      ((Ideal.Quotient.mk I).comp (ULift.ringEquiv.{u + 1, u + 1} (R := Λ)).toRingHom)
  have h₀ := NatTrans.congr_app (toSheafify_naturality (Scheme.ProEt.topology X)
    ((Functor.const X.ProEtᵒᵖ).map (CommRingCat.ofHom π))) (op U)
  have h := congrArg (fun φ => CommRingCat.Hom.hom φ (ULift.up l)) h₀
  simp only [NatTrans.comp_app, CommRingCat.hom_comp, RingHom.coe_comp,
    Function.comp_apply] at h
  refine h.symm.trans ?_
  have hπ : π (ULift.up l) = 0 := by
    show ULift.up (Ideal.Quotient.mk I l) = 0
    rw [(Ideal.Quotient.eq_zero_iff_mem).mpr hl]
    rfl
  show ((toSheafify (Scheme.ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj
    (CommRingCat.of (ULift.{u + 1} (Λ ⧸ I))))).app (op U)).hom (π (ULift.up l)) = 0
  rw [hπ]
  exact map_zero _

attribute [local instance] KoszulCompletion.derivedCountableProducts

/-- Over an affine weakly contractible object of `X_proétale`, the sections of a derived complete
sheaf of `Λ`-modules form a derived complete `Λ`-module. -/
theorem isDerivedCompleteModule_toCoefficientModuleSheaf_obj
    (F : RingedSite.Modules.{u + 1, u, u + 1} (constantCoefficientRingedSite.{u, u + 1, u} X Λ))
    (hF : RingedSite.IsDerivedComplete.{u + 1, u, u + 1, u + 1}
      (constantCoefficientRingedSite.{u, u + 1, u} X Λ)
      (constantCoefficientIdealSheaf.{u, u + 1, u} X Λ I)
      ((DerivedCategory.singleFunctor _ 0).obj F))
    (W : X.ProEt) (hW : IsAffine W.left ∧ (Scheme.ProEt.topology X).IsWeaklyContractible W) :
    IsDerivedCompleteModule I
      (ModuleCat.of Λ (((toCoefficientModuleSheaf.{u, u + 1, u} X Λ).obj F).obj.obj (op W))) := by
  have h := (RingedSite.isDerivedComplete_single_iff_sections_of_slicedObjectsSituation
    (constantCoefficientRingedSite.{u, u + 1, u} X Λ)
    (Scheme.ProEt.slicedObjectsSituation X (Stacks.SheafOfModules.Tensor.ringSheaf
      (constantCoefficientRingedSite.{u, u + 1, u} X Λ).O))
    (constantCoefficientIdealSheaf.{u, u + 1, u} X Λ I) F).mp hF W hW
  rw [DerivedCompleteRecurrence.isDerivedCompleteModule_iff_forall_bijective_recurrence] at h ⊢
  intro f hf
  have hb := h (constantCoefficientScalar X Λ W f) (constantCoefficientScalar_mem X Λ I W hf)
  have heq : ∀ a : ℕ → F.val.obj (op W),
      DerivedCompleteRecurrence.recurrence (M := ModuleCat.of Λ
        (((toCoefficientModuleSheaf.{u, u + 1, u} X Λ).obj F).obj.obj (op W))) f a =
      DerivedCompleteRecurrence.recurrence (M := F.val.obj (op W))
        (constantCoefficientScalar X Λ W f) a := by
    intro a
    funext n
    rw [DerivedCompleteRecurrence.recurrence_apply]
    exact congrArg (fun z => a n - z) (toCoefficientModuleSheaf_smul X Λ F W f (a (n + 1)))
  exact ⟨fun a b hab => hb.1 (((heq a).symm.trans hab).trans (heq b)),
    fun b => ⟨(hb.2 b).choose, (heq _).trans (hb.2 b).choose_spec⟩⟩

/-- **Maps out of a sheaf of `Λ`-modules read over the constant coefficient ring sheaf.** A map
of sheaves of `Λ`-modules from `G` to a sheaf of `Λ̲`-modules `F` read as a sheaf of `Λ`-modules
induces a map of sheaves of `Λ̲`-modules out of `G` read over `Λ̲`, with the same image on the
sections over every object. -/
theorem exists_moduleSheafOverConstantCoefficientsFunctor_hom
    (G : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))
    (F : RingedSite.Modules.{u + 1, u, u + 1} (constantCoefficientRingedSite.{u, u + 1, u} X Λ))
    (φ : G ⟶ (toCoefficientModuleSheaf.{u, u + 1, u} X Λ).obj F) :
    ∃ ψ : (moduleSheafOverConstantCoefficientsFunctor.{u, u + 1, u} X Λ).obj G ⟶ F,
      ∀ U : X.ProEt, Set.range (ψ.val.app (op U)) =
        Set.range (fun x : G.obj.obj (op U) =>
          (show F.val.obj (op U) from φ.hom.app (op U) x)) := by
  let a := constantCoefficientRingMap.{u, u + 1, u} X Λ
  let P := (modulePresheafOverConstantCoefficientsFunctor.{u, u + 1, u} X Λ).obj G
  let ψ₀ : P ⟶ (PresheafOfModules.restrictScalars a).obj F.val :=
    PresheafOfModules.homMk (Functor.whiskerRight φ.hom (forget₂ _ AddCommGrpCat.{u + 1}))
      (fun U r m => by
        show (φ.hom.app U).hom ((ULift.down r) • (show G.obj.obj U from m)) =
          (show F.val.obj U from a.app U r • (show F.val.obj U from (φ.hom.app U).hom m))
        rw [map_smul]
        exact toCoefficientModuleSheaf_smul X Λ F U.unop (ULift.down r) _)
  let ψ := (PresheafOfModules.sheafificationHomEquiv a).symm ψ₀
  have h := PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def a ψ
  have h2 := (congrArg (fun f => (PresheafOfModules.toPresheaf _).map f)
    (Equiv.apply_symm_apply (PresheafOfModules.sheafificationHomEquiv a) ψ₀)).symm.trans h
  have hsh : Presheaf.IsSheaf (Scheme.ProEt.topology X) P.presheaf :=
    GrothendieckTopology.HasSheafCompose.isSheaf (F := forget₂ (ModuleCat.{u + 1} Λ)
      AddCommGrpCat.{u + 1}) G.obj G.property
  have hiso : IsIso (CategoryTheory.toSheafify (Scheme.ProEt.topology X) P.presheaf) :=
    isIso_toSheafify _ hsh
  refine ⟨ψ, fun U => Set.ext fun z => ⟨fun ⟨y, hy⟩ => ?_, fun ⟨x, hx⟩ => ?_⟩⟩
  · have hsurj : Function.Surjective
        ((CategoryTheory.toSheafify (Scheme.ProEt.topology X) P.presheaf).app (op U)).hom :=
      ((ConcreteCategory.isIso_iff_bijective _).mp inferInstance).2
    obtain ⟨x, rfl⟩ := hsurj y
    exact ⟨x, (congrArg (fun f => (f.app (op U)).hom x) h2).trans hy⟩
  · exact ⟨((CategoryTheory.toSheafify (Scheme.ProEt.topology X) P.presheaf).app (op U)).hom x,
      (congrArg (fun f => (f.app (op U)).hom x) h2).symm.trans hx⟩

/-- Presheaves of modules in `Type (u + 1)` on the small pro-étale site of `X : Scheme.{u}` have
a sheafification. -/
theorem hasSheafify_proetale_moduleCat_succ (R : Type (u + 1)) [Ring R] :
    HasSheafify (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R) :=
  Stacks.ConstantSheaf.hasSheafify_moduleCat.{u + 1, u, u + 1, u} _ R

/-- Sheafification of presheaves of modules in `Type (u + 1)` on the small pro-étale site commutes
with the forgetful functor to types. -/
theorem preservesSheafification_proetale_forget_moduleCat_succ (R : Type (u + 1)) [Ring R] :
    (Scheme.ProEt.topology X).PreservesSheafification (forget (ModuleCat.{u + 1} R)) :=
  Stacks.ConstantSheaf.preservesSheafification_forget_moduleCat_of_univLE.{u + 1, u, u + 1, u + 1}
    _ R

attribute [local instance] hasSheafify_proetale_moduleCat_succ
  preservesSheafification_proetale_forget_moduleCat_succ

variable [IsNoetherianRing Λ]

/-- A global section of a sheaf of `Λ`-modules on `X_proétale` whose sections over the affine
weakly contractible objects are derived complete lies in the image of a map out of `Λ̲^∧`. -/
theorem exists_completedConstantSheaf_hom_mem_range
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))
    (hF : ∀ W : X.ProEt, IsAffine W.left ∧ (Scheme.ProEt.topology X).IsWeaklyContractible W →
      IsDerivedCompleteModule I (ModuleCat.of Λ (F.obj.obj (op W))))
    (s : F.obj.obj (op (Scheme.ProEt.mk (𝟙 X)))) :
    ∃ φ : Stacks.ConstantSheaf.completedConstantSheaf (Scheme.ProEt.topology X) I ⟶ F,
      s ∈ Set.range (φ.hom.app (op (Scheme.ProEt.mk (𝟙 X)))) := by
  let J := Scheme.ProEt.topology X
  let T := Scheme.ProEt.mk (𝟙 X)
  let adj := constantSheafAdj J (ModuleCat.{u + 1} Λ) (isTerminalProEtId X)
  let g : ModuleCat.of Λ Λ ⟶ F.obj.obj (op T) :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton Λ (F.obj.obj (op T)) s)
  let σ := (adj.homEquiv _ _).symm g
  have hσ : adj.unit.app (ModuleCat.of Λ Λ) ≫ σ.hom.app (op T) = g := by
    have := (adj.homEquiv _ _).apply_symm_apply g
    rwa [Adjunction.homEquiv_unit] at this
  obtain ⟨φ, hφ⟩ := (Stacks.ConstantSheaf.bijective_comp_completedConstantSheafStructureMap J I
    (fun W => IsAffine W.left ∧ J.IsWeaklyContractible W)
    (ProEtale.hasEnoughObjects_isAffine_isWeaklyContractible X) F hF).2 σ
  refine ⟨φ, (Stacks.ConstantSheaf.completedConstantSheafStructureMap J I).hom.app
    (op T) ((adj.unit.app (ModuleCat.of Λ Λ)).hom (1 : Λ)), ?_⟩
  have h1 := congrArg (fun f => (f.hom.app (op T)).hom
    ((adj.unit.app (ModuleCat.of Λ Λ)).hom (1 : Λ))) hφ
  have h2 := congrArg (fun f => f.hom (1 : Λ)) hσ
  simp only at h1 h2
  exact h1.trans (h2.trans (one_smul Λ s))

/-- **Maps out of the completed constant sheaf into a derived complete sheaf.** Let `X` be a
scheme, `Λ` a Noetherian ring, `I ⊂ Λ` an ideal and `F` a sheaf of `Λ̲`-modules on `X_proétale`
which is derived complete along `IΛ̲`. Every global section of `F` lies in the image of a map
`φ : Λ̲^∧ ⟶ F` of sheaves of `Λ̲`-modules. Moreover `φ` may be chosen to come from a map `φ'` of
sheaves of `Λ`-modules, with the same image on the sections over every object. -/
theorem exists_completedConstantSheaf_hom_of_isDerivedComplete
    (F : RingedSite.Modules.{u + 1, u, u + 1} (constantCoefficientRingedSite.{u, u + 1, u} X Λ))
    (hF : RingedSite.IsDerivedComplete.{u + 1, u, u + 1, u + 1}
      (constantCoefficientRingedSite.{u, u + 1, u} X Λ)
      (constantCoefficientIdealSheaf.{u, u + 1, u} X Λ I)
      ((DerivedCategory.singleFunctor _ 0).obj F))
    (s : F.val.obj (op (Scheme.ProEt.mk (𝟙 X)))) :
    ∃ (φ' : Stacks.ConstantSheaf.completedConstantSheaf (Scheme.ProEt.topology X) I ⟶
        (toCoefficientModuleSheaf.{u, u + 1, u} X Λ).obj F)
      (φ : (moduleSheafOverConstantCoefficientsFunctor.{u, u + 1, u} X Λ).obj
        (Stacks.ConstantSheaf.completedConstantSheaf (Scheme.ProEt.topology X) I) ⟶ F),
      s ∈ Set.range (φ.val.app (op (Scheme.ProEt.mk (𝟙 X)))) ∧
      ∀ U : X.ProEt, Set.range (φ.val.app (op U)) =
        Set.range (fun x => (show F.val.obj (op U) from φ'.hom.app (op U) x)) := by
  obtain ⟨φ', x, hx⟩ := exists_completedConstantSheaf_hom_mem_range X Λ I
    ((toCoefficientModuleSheaf.{u, u + 1, u} X Λ).obj F)
    (fun W hW => isDerivedCompleteModule_toCoefficientModuleSheaf_obj X Λ I F hF W hW) s
  obtain ⟨φ, hφ⟩ := exists_moduleSheafOverConstantCoefficientsFunctor_hom X Λ _ F φ'
  refine ⟨φ', φ, ?_, hφ⟩
  rw [hφ]
  exact ⟨x, hx⟩

end AlgebraicGeometry.ProEtale
