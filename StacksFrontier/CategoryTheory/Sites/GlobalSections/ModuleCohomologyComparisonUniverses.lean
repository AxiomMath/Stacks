module

public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparisonDef
public import Mathlib.Algebra.Category.Grp.Limits
import all StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparison

/-!
# Stacks 03FD for global sections at independent site, ring and coefficient universes

The global-sections half of [Stacks, Tag 03FD]: deriving the global sections of a sheaf of
modules and then forgetting agrees, in every degree, with forgetting to an abelian sheaf and
deriving global sections there. The universes are independent: the objects of the site lie in
`Type u`, its morphisms in `Type v`, the sheaf of rings has sections in `Type r`, and the abelian
sheaves and module sheaves have sections in `Type (max u r m)`.

## Main definitions

* `ModuleSheafCohomology.Univ.tensorPresheaf`: extension of scalars `F ↦ R ⊗[ℤ] F` from abelian
  presheaves at `Ab.{max u t}` to module presheaves over a presheaf of rings at `RingCat.{u}`,
  with its functoriality, its unit and the adjunction `tensorPresheafHomAddEquiv`.
* `ModuleSheafCohomology.Univ.tensorSheafHomIso`: morphisms out of the sheafified extension of
  scalars of `P` are morphisms out of the sheafification of `P` into the underlying abelian
  sheaf.
* `ModuleSheafCohomology.Univ.globalSectionsRepresentation`: global sections of abelian sheaves
  are corepresented by the constant sheaf on `ℤ`.
* `ModuleSheafCohomology.Univ.globalSectionsComparisonIso`: the comparison of the derived functors
  of global sections of module sheaves and of abelian sheaves, as an isomorphism in every degree,
  with its degree-zero normalization
  `ModuleSheafCohomology.Univ.toRightDerivedZero_comp_globalSectionsComparisonIso`.

## Main results

* `ModuleSheafCohomology.Univ.ext_eq_zero_of_isTorsionFree`: the underlying abelian sheaf of an
  injective module sheaf is `Ext`-acyclic against every sectionwise torsion-free sheaf.

## References

* [Stacks: Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Limits CategoryTheory.Abelian

namespace ModuleSheafCohomology.Univ

section TensorPresheaf

universe t w v u

open TensorProduct

variable {D : Type w} [Category.{v} D] (R : Dᵒᵖ ⥤ RingCat.{u})

/-- Restriction along `f` in the extension of scalars of an abelian presheaf, as a semilinear
map over the restriction of the presheaf of rings. -/
public def tensorPresheafRestrict (F : Dᵒᵖ ⥤ Ab.{max u t}) {X Y : Dᵒᵖ} (f : X ⟶ Y) :
    (R.obj X ⊗[ℤ] F.obj X) →ₛₗ[(R.map f).hom] (R.obj Y ⊗[ℤ] F.obj Y) where
  toFun := TensorProduct.map (R.map f).hom.toAddMonoidHom.toIntLinearMap
    (F.map f).hom.toIntLinearMap
  map_add' := map_add _
  map_smul' r x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
    | tmul a x => simp [TensorProduct.smul_tmul', smul_eq_mul]

/-- `tensorPresheafRestrict` on elementary tensors. -/
public lemma tensorPresheafRestrict_tmul (F : Dᵒᵖ ⥤ Ab.{max u t})
    {X Y : Dᵒᵖ} (f : X ⟶ Y) (r : R.obj X) (x : F.obj X) :
    tensorPresheafRestrict R F f (r ⊗ₜ[ℤ] x) = R.map f r ⊗ₜ[ℤ] F.map f x :=
  TensorProduct.map_tmul _ _ _ _

/-- Extension of scalars from abelian presheaves to module presheaves, on objects. -/
public def tensorPresheaf (F : Dᵒᵖ ⥤ Ab.{max u t}) : PresheafOfModules.{max u t} R where
  obj X := ModuleCat.of (R.obj X) (R.obj X ⊗[ℤ] F.obj X)
  map f := (ModuleCat.semilinearMapAddEquiv (R.map f).hom _ _)
    (tensorPresheafRestrict R F f)
  map_id X := by
    apply ModuleCat.hom_ext
    apply TensorProduct.AlgebraTensorModule.ext
    intro a x
    change tensorPresheafRestrict R F (𝟙 X) (a ⊗ₜ[ℤ] x) = a ⊗ₜ[ℤ] x
    simp [tensorPresheafRestrict_tmul]
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply TensorProduct.AlgebraTensorModule.ext
    intro a x
    change tensorPresheafRestrict R F (f ≫ g) (a ⊗ₜ[ℤ] x) =
      tensorPresheafRestrict R F g (tensorPresheafRestrict R F f (a ⊗ₜ[ℤ] x))
    simp [tensorPresheafRestrict_tmul]

/-- Restriction in the extension of scalars of an abelian presheaf, on elementary tensors. -/
public lemma tensorPresheaf_map_tmul (F : Dᵒᵖ ⥤ Ab.{max u t})
    {X Y : Dᵒᵖ} (f : X ⟶ Y) (r : R.obj X) (x : F.obj X) :
    (tensorPresheaf R F).map f (r ⊗ₜ[ℤ] x) = R.map f r ⊗ₜ[ℤ] F.map f x :=
  TensorProduct.map_tmul _ _ _ _

/-- Extension of scalars on a morphism of abelian presheaves. -/
public def tensorPresheafMap {F G : Dᵒᵖ ⥤ Ab.{max u t}} (f : F ⟶ G) :
    tensorPresheaf R F ⟶ tensorPresheaf R G where
  app X := ModuleCat.ofHom (AlgebraTensorModule.map (LinearMap.id : R.obj X →ₗ[R.obj X] R.obj X)
    (f.app X).hom.toIntLinearMap)
  naturality {X Y} g := by
    apply ModuleCat.hom_ext
    apply TensorProduct.AlgebraTensorModule.ext
    intro r x
    change R.map g r ⊗ₜ[ℤ] f.app Y (F.map g x) =
      R.map g r ⊗ₜ[ℤ] G.map g (f.app X x)
    rw [NatTrans.naturality_apply]

private lemma tensorPresheafMap_app_tmul {F G : Dᵒᵖ ⥤ Ab.{max u t}} (f : F ⟶ G)
    (X : Dᵒᵖ) (r : R.obj X) (x : F.obj X) :
    (tensorPresheafMap R f).app X (r ⊗ₜ[ℤ] x) = r ⊗ₜ[ℤ] f.app X x := rfl

/-- An additive morphism extends uniquely to an `R`-linear morphism from its tensor product. -/
public def tensorPresheafLift {F : Dᵒᵖ ⥤ Ab.{max u t}} {M : PresheafOfModules.{max u t} R}
    (f : F ⟶ M.presheaf) : tensorPresheaf R F ⟶ M where
  app X := ModuleCat.ofHom
    (X := (tensorPresheaf R F).obj X) (Y := M.obj X)
    (AlgebraTensorModule.lift
      (LinearMap.toSpanSingleton (R.obj X) (F.obj X →ₗ[ℤ] M.obj X)
        (f.app X).hom.toIntLinearMap))
  naturality {X Y} g := by
    apply ModuleCat.hom_ext
    apply TensorProduct.AlgebraTensorModule.ext
    intro r x
    change R.map g r • (show M.obj Y from f.app Y (F.map g x)) =
      M.map g (r • (show M.obj X from f.app X x))
    rw [M.map_smul, NatTrans.naturality_apply]
    rfl

/-- `tensorPresheafLift` on elementary tensors. -/
public lemma tensorPresheafLift_app_tmul {F : Dᵒᵖ ⥤ Ab.{max u t}}
    {M : PresheafOfModules.{max u t} R} (f : F ⟶ M.presheaf)
    (X : Dᵒᵖ) (r : R.obj X) (x : F.obj X) :
    (tensorPresheafLift R f).app X (r ⊗ₜ[ℤ] x) = r • f.app X x := rfl

/-- The canonical additive map into extension of scalars. -/
public def tensorPresheafUnit (F : Dᵒᵖ ⥤ Ab.{max u t}) :
    F ⟶ (tensorPresheaf R F).presheaf where
  app X := AddCommGrpCat.ofHom ((TensorProduct.mk ℤ (R.obj X) (F.obj X) 1).toAddMonoidHom)
  naturality {X Y} f := by
    ext x
    change 1 ⊗ₜ[ℤ] F.map f x = (tensorPresheaf R F).map f (1 ⊗ₜ[ℤ] x)
    rw [tensorPresheaf_map_tmul, map_one]

/-- The canonical map into extension of scalars followed by `tensorPresheafLift f` is `f`. -/
public lemma tensorPresheafUnit_comp_lift {F : Dᵒᵖ ⥤ Ab.{max u t}}
    {M : PresheafOfModules.{max u t} R} (f : F ⟶ M.presheaf) :
    tensorPresheafUnit R F ≫ (PresheafOfModules.toPresheaf R).map
      (tensorPresheafLift R f) = f := by
  ext X x
  show (tensorPresheafLift R f).app X (1 ⊗ₜ[ℤ] x) = f.app X x
  rw [tensorPresheafLift_app_tmul, one_smul]

/-- The canonical map into extension of scalars is natural in the abelian presheaf. -/
public lemma tensorPresheafUnit_naturality {F G : Dᵒᵖ ⥤ Ab.{max u t}} (f : F ⟶ G) :
    f ≫ tensorPresheafUnit R G = tensorPresheafUnit R F ≫
      (PresheafOfModules.toPresheaf R).map (tensorPresheafMap R f) := by
  ext X x
  rfl

/-- The tensor presheaf represents additive maps from the original abelian presheaf. -/
public def tensorPresheafHomAddEquiv (F : Dᵒᵖ ⥤ Ab.{max u t})
    (M : PresheafOfModules.{max u t} R) :
    (tensorPresheaf R F ⟶ M) ≃+ (F ⟶ M.presheaf) where
  toFun f := tensorPresheafUnit R F ≫ (PresheafOfModules.toPresheaf R).map f
  invFun := tensorPresheafLift R
  left_inv f := by
    ext1 X
    apply ModuleCat.hom_ext
    apply TensorProduct.AlgebraTensorModule.ext
    intro r x
    change r • f.app X (1 ⊗ₜ[ℤ] x) = f.app X (r ⊗ₜ[ℤ] x)
    change r • (f.app X).hom (1 ⊗ₜ[ℤ] x) = (f.app X).hom (r ⊗ₜ[ℤ] x)
    calc
      _ = (f.app X).hom (r • (1 ⊗ₜ[ℤ] x)) :=
        ((f.app X).hom.map_smul r (1 ⊗ₜ[ℤ] x)).symm
      _ = _ := by
        congr 1
        change (r * 1) ⊗ₜ[ℤ] x = r ⊗ₜ[ℤ] x
        rw [mul_one]
  right_inv := tensorPresheafUnit_comp_lift R
  map_add' f g := by
    ext X x
    rfl

/-- `tensorPresheafHomAddEquiv` turns precomposition with `tensorPresheafMap p` into
precomposition with `p`. -/
private lemma tensorPresheafHomAddEquiv_map_comp {F G : Dᵒᵖ ⥤ Ab.{max u t}} (p : F ⟶ G)
    {M : PresheafOfModules.{max u t} R} (g : tensorPresheaf R G ⟶ M) :
    tensorPresheafHomAddEquiv R F M (tensorPresheafMap R p ≫ g) =
      p ≫ tensorPresheafHomAddEquiv R G M g := by
  change tensorPresheafUnit R F ≫ (PresheafOfModules.toPresheaf R).map (tensorPresheafMap R p ≫ g)
    = p ≫ tensorPresheafUnit R G ≫ (PresheafOfModules.toPresheaf R).map g
  rw [Functor.map_comp]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ (PresheafOfModules.toPresheaf R).map g)
      (tensorPresheafUnit_naturality R p).symm).trans (Category.assoc _ _ _))

end TensorPresheaf

universe m r u v

section SiteGeneral

universe w

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J Ab.{w}] [J.WEqualsLocallyBijective Ab.{w}]
  [HasGlobalSectionsFunctor J Ab.{w}]

/-- The underlying presheaf of modules of an injective module sheaf is injective. -/
public theorem injective_forget_obj
    {D : Type*} [Category D] {K : GrothendieckTopology D}
    (R : Sheaf K RingCat.{r}) [HasSheafify K Ab.{v}]
    [K.WEqualsLocallyBijective Ab.{v}]
    (I : SheafOfModules.{v} R) [Injective I] :
    Injective ((SheafOfModules.forget R).obj I) :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).map_injective I inferInstance

/-- Abelian presheaves have products indexed by `Type w`, stated directly so that instance search
does not time out. -/
local instance hasLimitsOfShape_discrete_presheaf (K : Type w) :
    HasLimitsOfShape (Discrete K) (Cᵒᵖ ⥤ Ab.{w}) :=
  functorCategoryHasLimitsOfShape

/-- Global sections of abelian sheaves form an additive functor. -/
local instance gamma_additive : (Sheaf.Γ J Ab.{w}).Additive :=
  have : HasBinaryProducts (Sheaf J Ab.{w}) :=
    hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (sheafToPresheaf J Ab.{w})
  Functor.additive_of_preserves_binary_products _

/-- The forgetful functor from module sheaves to abelian sheaves preserves finite colimits. -/
local instance toSheaf_preservesFiniteColimits (R : Sheaf J RingCat.{r}) :
    PreservesFiniteColimits (SheafOfModules.toSheaf.{w} R) := by
  let sheafification := PresheafOfModules.sheafification (𝟙 R.obj)
  let adjunction := PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)
  let counitIso := asIso adjunction.counit
  have composite : PreservesFiniteColimits (sheafification ⋙ SheafOfModules.toSheaf R) :=
    preservesFiniteColimits_of_natIso
      (PresheafOfModules.sheafificationCompToSheaf (𝟙 R.obj)).symm
  let : PreservesColimitsOfSize.{0, 0} sheafification :=
    adjunction.leftAdjoint_preservesColimits
  refine ⟨fun {index} _ _ ↦ ⟨fun {diagram} ↦ ?_⟩⟩
  let forgetful := SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)
  have comparison : (diagram ⋙ forgetful) ⋙ sheafification ≅ diagram :=
    NatIso.ofComponents (fun point ↦ counitIso.app (diagram.obj point))
      (fun map ↦ counitIso.hom.naturality (diagram.map map))
  have : PreservesColimit (diagram ⋙ forgetful)
      (sheafification ⋙ SheafOfModules.toSheaf R) :=
    (composite.preservesFiniteColimits index).preservesColimit
  have : PreservesColimit ((diagram ⋙ forgetful) ⋙ sheafification)
      (SheafOfModules.toSheaf R) :=
    preservesColimit_of_preserves_colimit_cocone
      (isColimitOfPreserves sheafification (colimit.isColimit (diagram ⋙ forgetful)))
      (isColimitOfPreserves (sheafification ⋙ SheafOfModules.toSheaf R)
        (colimit.isColimit (diagram ⋙ forgetful)))
  exact preservesColimit_of_iso_diagram _ comparison

end SiteGeneral

section SiteTensor

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J Ab.{max u r m}] [J.WEqualsLocallyBijective Ab.{max u r m}]
  [HasExt.{max u r m} (Sheaf J Ab.{max u r m})]
  [HasInjectiveResolutions (Sheaf J Ab.{max u r m})]

attribute [local instance] gamma_additive toSheaf_preservesFiniteColimits

omit [J.WEqualsLocallyBijective Ab.{max u r m}] [HasExt.{max u r m} (Sheaf J Ab.{max u r m})]
  [HasInjectiveResolutions (Sheaf J Ab.{max u r m})] in
/-- Tensoring a short exact sequence with sectionwise torsion-free quotient preserves
the inclusion on the underlying presheaves. -/
private lemma mono_tensorPresheafMap_of_shortExact
    (R : Cᵒᵖ ⥤ RingCat.{r}) (S : ShortComplex (Sheaf J Ab.{max u r m}))
    (hS : S.ShortExact) (hP : ∀ X, Module.IsTorsionFree ℤ (S.X₃.obj.obj X)) :
    Mono (tensorPresheafMap.{max u m} R S.f.hom) := by
  have := hS.mono_f
  apply PresheafOfModules.mono_of_injective
  intro X
  have := hP X
  let E := sheafToPresheaf J Ab.{max u r m} ⋙ (evaluation Cᵒᵖ Ab.{max u r m}).obj X
  have hE : (S.map E).Exact :=
    ((Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono E).mp
      inferInstance S hS).1
  exact lTensor_injective_of_exact_of_isTorsionFree
    (S.f.hom.app X).hom.toIntLinearMap (S.g.hom.app X).hom.toIntLinearMap
    ((AddCommGrpCat.mono_iff_injective _).mp inferInstance)
    ((ShortComplex.ab_exact_iff_function_exact (S.map E)).mp hE) (R.obj X)

omit [HasExt.{max u r m} (Sheaf J Ab.{max u r m})]
  [HasInjectiveResolutions (Sheaf J Ab.{max u r m})] in
/-- Maps to the underlying abelian sheaf of an injective module sheaf extend across
short exact sequences with sectionwise torsion-free quotient. -/
public lemma exists_extension_of_isTorsionFree
    (R : Sheaf J RingCat.{r}) (I : SheafOfModules.{max u r m} R) [Injective I]
    (S : ShortComplex (Sheaf J Ab.{max u r m})) (hS : S.ShortExact)
    (hP : ∀ X, Module.IsTorsionFree ℤ (S.X₃.obj.obj X))
    (f : S.X₁ ⟶ (SheafOfModules.toSheaf R).obj I) :
    ∃ g : S.X₂ ⟶ (SheafOfModules.toSheaf R).obj I, S.f ≫ g = f := by
  have : Injective I.val := injective_forget_obj R I
  have := mono_tensorPresheafMap_of_shortExact.{m} J R.obj S hS hP
  let g := Injective.factorThru (tensorPresheafLift R.obj f.hom)
    (tensorPresheafMap R.obj S.f.hom)
  refine ⟨⟨tensorPresheafUnit R.obj S.X₂.obj ≫
    (PresheafOfModules.toPresheaf R.obj).map g⟩, ?_⟩
  have key : tensorPresheafMap R.obj S.f.hom ≫ g = tensorPresheafLift R.obj f.hom :=
    Injective.comp_factorThru _ _
  apply Sheaf.hom_ext
  change S.f.hom ≫ tensorPresheafHomAddEquiv.{max u m} R.obj S.X₂.obj _ g = f.hom
  rw [← tensorPresheafHomAddEquiv_map_comp, key]
  exact tensorPresheafUnit_comp_lift.{max u m} R.obj f.hom

/-- The underlying abelian sheaf of an injective module sheaf is Ext-acyclic against
every sectionwise torsion-free sheaf. -/
public lemma ext_eq_zero_of_isTorsionFree
    (R : Sheaf J RingCat.{r}) (I : SheafOfModules.{max u r m} R) [Injective I]
    (X : Sheaf J Ab.{max u r m}) (hX : ∀ U, Module.IsTorsionFree ℤ (X.obj.obj U))
    (n : ℕ) (e : Ext.{max u r m} X ((SheafOfModules.toSheaf R).obj I) (n + 1)) : e = 0 :=
  ext_eq_zero_of_resolving (fun F : Sheaf J Ab.{max u r m} ↦
    ∀ U, Module.IsTorsionFree ℤ (F.obj.obj U)) (fun f _ hG ↦ isTorsionFree_of_mono J f hG)
    (exists_isTorsionFree_epi J) ((SheafOfModules.toSheaf R).obj I)
    (ext_one_eq_zero_of_extension _ _ (exists_extension_of_isTorsionFree.{m} J R I)) n X hX e

/-- The functor of sections over `U` on abelian sheaves is additive. -/
local instance (U : C) : ((sheafSections J Ab.{max u r m}).obj (op U)).Additive where
  map_add := by intros; rfl

/-- The functor of sections over `U` on abelian sheaves preserves finite limits. -/
local instance (U : C) :
    PreservesFiniteLimits ((sheafSections J Ab.{max u r m}).obj (op U)) :=
  preservesFiniteLimits_of_natIso (sheafSectionsNatIsoEvaluation J Ab.{max u r m}).symm

omit [HasExt.{max u r m} (Sheaf J Ab.{max u r m})]
  [HasInjectiveResolutions (Sheaf J Ab.{max u r m})] in
/-- Naturality in the module sheaf of the composite of the sheafification adjunction of module
presheaves, the extension of scalars `tensorPresheafHomAddEquiv`, and the sheafification
adjunction of abelian presheaves. -/
private lemma tensorSheafHom_naturality_aux (R : Sheaf J RingCat.{r})
    (P : Cᵒᵖ ⥤ Ab.{max u r m}) {M N : SheafOfModules.{max u r m} R} (map : M ⟶ N)
    (element : (PresheafOfModules.sheafification (𝟙 R.obj)).obj
      (tensorPresheaf.{max u m} R.obj P) ⟶ M) :
    ((sheafificationAdjunction J Ab.{max u r m}).homEquiv P
        ((SheafOfModules.toSheaf R).obj N)).symm
      (tensorPresheafUnit.{max u m} R.obj P ≫ (PresheafOfModules.toPresheaf R.obj).map
        ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv _ N
          (element ≫ map))) =
    ((sheafificationAdjunction J Ab.{max u r m}).homEquiv P
        ((SheafOfModules.toSheaf R).obj M)).symm
      (tensorPresheafUnit.{max u m} R.obj P ≫ (PresheafOfModules.toPresheaf R.obj).map
        ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv _ M element)) ≫
      (SheafOfModules.toSheaf R).map map := by
  rw [Adjunction.homEquiv_naturality_right]
  refine (congrArg (fun z ↦ ((sheafificationAdjunction J Ab.{max u r m}).homEquiv P
      ((SheafOfModules.toSheaf R).obj N)).symm (tensorPresheafUnit.{max u m} R.obj P ≫ z))
      ((PresheafOfModules.toPresheaf R.obj).map_comp _ _)).trans ?_
  refine (congrArg ((sheafificationAdjunction J Ab.{max u r m}).homEquiv P
      ((SheafOfModules.toSheaf R).obj N)).symm (Category.assoc _ _ _).symm).trans ?_
  exact (sheafificationAdjunction J Ab.{max u r m}).homEquiv_naturality_right_symm
    (g := (SheafOfModules.toSheaf R).map map) _

/-- Morphisms out of the sheafified extension of scalars of an abelian presheaf `P` are the
morphisms out of the sheafification of `P` into the underlying abelian sheaf. -/
@[no_expose]
public def tensorSheafHomIso (R : Sheaf J RingCat.{r})
    (P : Cᵒᵖ ⥤ Ab.{max u r m}) :
    preadditiveCoyoneda.obj (op
      ((PresheafOfModules.sheafification (𝟙 R.obj)).obj
        (tensorPresheaf.{max u m} R.obj P))) ≅
    SheafOfModules.toSheaf R ⋙ preadditiveCoyoneda.obj
      (op ((presheafToSheaf J Ab.{max u r m}).obj P)) := by
  have : (PresheafOfModules.sheafification (𝟙 R.obj)).Additive :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).left_adjoint_additive
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · exact (((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homAddEquiv
      (tensorPresheaf R.obj P) M).trans
      ((tensorPresheafHomAddEquiv R.obj P
        ((SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)).obj M)).trans
        ((sheafificationAdjunction J Ab.{max u r m}).homAddEquiv P
          ((SheafOfModules.toSheaf R).obj M)).symm)).toAddCommGrpIso
  · intro M N map
    ext element
    change ((PresheafOfModules.sheafification (𝟙 R.obj)).obj
      (tensorPresheaf R.obj P) ⟶ M) at element
    exact tensorSheafHom_naturality_aux J R P map element

omit [HasExt.{max u r m} (Sheaf J Ab.{max u r m})]
  [HasInjectiveResolutions (Sheaf J Ab.{max u r m})] in
/-- `tensorSheafHomIso` is natural in the abelian presheaf: for a morphism `p : P ⟶ P'` of
abelian presheaves, it intertwines precomposition with the sheafification of
`tensorPresheafMap p` and precomposition with `presheafToSheaf.map p`. -/
public lemma tensorSheafHomIso_naturality (R : Sheaf J RingCat.{r})
    {P P' : Cᵒᵖ ⥤ Ab.{max u r m}} (p : P ⟶ P') :
    preadditiveCoyoneda.map
        ((PresheafOfModules.sheafification (𝟙 R.obj)).map
          (tensorPresheafMap.{max u m} R.obj p)).op ≫
        (tensorSheafHomIso J R P).hom =
      (tensorSheafHomIso J R P').hom ≫
        Functor.whiskerLeft (SheafOfModules.toSheaf R)
          (preadditiveCoyoneda.map ((presheafToSheaf J Ab.{max u r m}).map p).op) := by
  refine NatTrans.ext (funext fun M ↦ ?_)
  ext element
  change ((PresheafOfModules.sheafification (𝟙 R.obj)).obj (tensorPresheaf R.obj P') ⟶ M)
    at element
  show ((sheafificationAdjunction J Ab.{max u r m}).homEquiv P
        ((SheafOfModules.toSheaf R).obj M)).symm
        ((tensorPresheafHomAddEquiv R.obj P
          ((SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)).obj M))
          ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv _ M
            ((PresheafOfModules.sheafification (𝟙 R.obj)).map (tensorPresheafMap R.obj p) ≫
              element))) =
      (presheafToSheaf J Ab.{max u r m}).map p ≫
        ((sheafificationAdjunction J Ab.{max u r m}).homEquiv P'
          ((SheafOfModules.toSheaf R).obj M)).symm
          ((tensorPresheafHomAddEquiv R.obj P'
            ((SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)).obj M))
            ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv _ M element))
  have key : (tensorPresheafHomAddEquiv R.obj P
        ((SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)).obj M))
        ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv
          (tensorPresheaf R.obj P) M
          ((PresheafOfModules.sheafification (𝟙 R.obj)).map (tensorPresheafMap R.obj p) ≫
            element)) =
      p ≫ (tensorPresheafHomAddEquiv R.obj P'
        ((SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)).obj M))
        ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv
          (tensorPresheaf R.obj P') M element) := by
    rw [Adjunction.homEquiv_naturality_left]
    exact tensorPresheafHomAddEquiv_map_comp R.obj p _
  exact (congrArg (fun m ↦ ((sheafificationAdjunction J Ab.{max u r m}).homEquiv P
      ((SheafOfModules.toSheaf R).obj M)).symm m) key).trans
    ((sheafificationAdjunction J Ab.{max u r m}).homEquiv_naturality_left_symm p _)

/-- A corepresented additive functor on abelian sheaves, whose corepresenting object is the
sheafification of a sectionwise torsion-free presheaf, commutes in positive degree with deriving
after the forgetful functor from module sheaves. -/
private theorem represented_succ_comparison (R : Sheaf J RingCat.{r})
    [HasExt.{max u r m} (SheafOfModules.{max u r m} R)]
    [EnoughInjectives (SheafOfModules.{max u r m} R)]
    (P : Cᵒᵖ ⥤ Ab.{max u r m}) (hP : ∀ point, Module.IsTorsionFree ℤ (P.obj point))
    (G : Sheaf J Ab.{max u r m} ⥤ Ab.{max u r m}) [G.Additive]
    (representation : G ≅ preadditiveCoyoneda.obj
      (op ((presheafToSheaf J Ab.{max u r m}).obj P))) (degree : ℕ) :
    Nonempty ((SheafOfModules.toSheaf R ⋙ G).rightDerived (degree + 1) ≅
      SheafOfModules.toSheaf R ⋙ G.rightDerived (degree + 1)) := by
  refine ⟨rightDerivedCompIsoOfRepresentable (SheafOfModules.toSheaf.{max u r m} R) G
    ((presheafToSheaf J Ab.{max u r m}).obj P)
    ((PresheafOfModules.sheafification (𝟙 R.obj)).obj (tensorPresheaf.{max u m} R.obj P))
    ?_ representation (tensorSheafHomIso J R P) degree⟩
  intro injectiveObject instanceInjective index extension
  exact ext_eq_zero_of_isTorsionFree.{m} J R injectiveObject _
    (isTorsionFree_sheafify J P hP) index extension

/-- Global sections of abelian sheaves are corepresented by the constant sheaf on `ℤ`. -/
public def globalSectionsRepresentation :
    Sheaf.Γ J Ab.{max u r m} ≅ preadditiveCoyoneda.obj
      (op ((constantSheaf J Ab.{max u r m}).obj (AddCommGrpCat.of (ULift.{max u r m} ℤ)))) := by
  refine (NatIso.ofComponents (fun F ↦
    (((constantSheafΓAdj J Ab.{max u r m}).homAddEquiv
      (AddCommGrpCat.of (ULift.{max u r m} ℤ)) F).trans
      (AddCommGrpCat.uliftZMultiplesAddEquiv _)).toAddCommGrpIso) ?_).symm
  intro F G map
  ext element
  change ((constantSheaf J Ab.{max u r m}).obj (AddCommGrpCat.of (ULift.{max u r m} ℤ)) ⟶ F)
    at element
  change ((constantSheafΓAdj J Ab.{max u r m}).homEquiv _ G (element ≫ map)) (ULift.up (1 : ℤ)) =
    ((Sheaf.Γ J Ab.{max u r m}).map map)
      (((constantSheafΓAdj J Ab.{max u r m}).homEquiv _ F element) (ULift.up (1 : ℤ)))
  rw [Adjunction.homEquiv_naturality_right]
  rfl

end SiteTensor

section SiteGlobal

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (R : Sheaf J RingCat.{r})
  [HasSheafify J Ab.{max u r m}] [J.WEqualsLocallyBijective Ab.{max u r m}]
  [HasExt.{max u r m} (Sheaf J Ab.{max u r m})]
  [HasInjectiveResolutions (Sheaf J Ab.{max u r m})]
  [HasExt.{max u r m} (SheafOfModules.{max u r m} R)]
  [HasInjectiveResolutions (SheafOfModules.{max u r m} R)]
  [EnoughInjectives (SheafOfModules.{max u r m} R)]

attribute [local instance] gamma_additive toSheaf_preservesFiniteColimits

/-- Deriving the global sections of a sheaf of modules and then forgetting agrees, in every
degree, with forgetting to an abelian sheaf and deriving global sections there. -/
def globalSectionsComparisonIso (n : ℕ) :
    (SheafOfModules.toSheaf.{max u r m} R ⋙ Sheaf.Γ J Ab.{max u r m}).rightDerived n ≅
      SheafOfModules.toSheaf.{max u r m} R ⋙ (Sheaf.Γ J Ab.{max u r m}).rightDerived n :=
  comparisonIso (SheafOfModules.toSheaf.{max u r m} R) (Sheaf.Γ J Ab.{max u r m}) _
    (globalSectionsRepresentation.{m, r, u, v} J)
    ((PresheafOfModules.sheafification (𝟙 R.obj)).obj
      (tensorPresheaf.{max u m} R.obj
        ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{max u r m} ℤ)))))
    (tensorSheafHomIso.{m, r, u, v} J R
      ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{max u r m} ℤ))))
    (fun I _ index extension ↦
      ext_eq_zero_of_isTorsionFree.{m, r, u, v} J R I _
        (isTorsionFree_sheafify J
          ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{max u r m} ℤ)))
          (fun _ ↦ by
            change Module.IsTorsionFree ℤ (ULift.{max u r m} ℤ)
            exact Module.Flat.isTorsionFree)) index extension)
    n

/-- The degree-zero normalization of `globalSectionsComparisonIso`. -/
lemma toRightDerivedZero_comp_globalSectionsComparisonIso :
    (SheafOfModules.toSheaf.{max u r m} R ⋙ Sheaf.Γ J Ab.{max u r m}).toRightDerivedZero ≫
        (globalSectionsComparisonIso.{m, r, u, v} J R 0).hom =
      Functor.whiskerLeft (SheafOfModules.toSheaf.{max u r m} R)
        (Sheaf.Γ J Ab.{max u r m}).toRightDerivedZero :=
  toRightDerivedZero_comp_comparisonIso _ _ _ _ _ _ _

end SiteGlobal

end ModuleSheafCohomology.Univ

end
