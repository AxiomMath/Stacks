module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuotientStackChartPointSection
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuotientStackOfGroupoidModule
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleDenseSubsite
public import StacksFrontier.AlgebraicGeometry.QcohRestrictEquiv.IsoLocality

/-!
# The module of the quasi-coherent module on `[U/R]` attached to `(𝒢, α)`

Let `(𝒢, α)` be a quasi-coherent module on a groupoid `(U, R, s, t, c)` in algebraic spaces and
let `ℱ` be the quasi-coherent module on `[U/R]` built from it
(`AlgebraicGeometry.Stack.quotientStackModuleOfGroupoid`). This file identifies the module
`x^*ℱ|_{U_étale}` of the image of `ℱ` under the functor of Stacks 06WT with `𝒢`: over an affine
étale chart `W` of `U`, `ℱ(x(u_W)) ≅ Γ(W, u_W^*𝒢) ≅ 𝒢(W)`, the first isomorphism by construction
of `ℱ` and the second the chart section along `u_W`; these are natural in `W`, and the affine
charts are a dense subsite of `U_étale` (Stacks 04JS).

## Main definitions

* `AlgebraicGeometry.Stack.quotientStackModuleOfGroupoidHom`: the morphism
  `𝒢 ⟶ x^*ℱ|_{U_étale}`.

## Main results

* `AlgebraicGeometry.Stack.isIso_quotientStackModuleOfGroupoidHom`: it is an isomorphism.

## References

* [Stacks Project, Tag 06WT](https://stacks.math.columbia.edu/tag/06WT)
* [Stacks Project, Tag 04JS](https://stacks.math.columbia.edu/tag/04JS)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u w u₁ v₁ u₂ v₂

/-- A morphism of presheaves of modules from additive maps which are natural and linear on
elements. -/
noncomputable def Stacks.PresheafOfModules.homOfApply {D : Type*} [Category D]
    {R : Dᵒᵖ ⥤ RingCat.{w}} {M₁ M₂ : PresheafOfModules.{w} R} (f : ∀ X, M₁.obj X →+ M₂.obj X)
    (nat : ∀ {X Y : Dᵒᵖ} (g : X ⟶ Y) (x : M₁.obj X), f Y (M₁.map g x) = M₂.map g (f X x))
    (smul : ∀ (X : Dᵒᵖ) (r : R.obj X) (m : M₁.obj X), f X (r • m) = r • f X m) : M₁ ⟶ M₂ :=
  PresheafOfModules.homMk
    { app := fun X => AddCommGrpCat.ofHom (f X)
      naturality := fun X Y g => by
        ext x
        exact nat g x }
    smul

namespace Stacks.DenseSubsiteModules

variable {C₁ : Type u₁} [Category.{v₁} C₁] {C' : Type u₂} [Category.{v₂} C']
  (J : GrothendieckTopology C₁) (K : GrothendieckTopology C') (v : C₁ ⥤ C') [v.IsDenseSubsite J K]
  (R : Sheaf K RingCat.{w})

/-- The components of the inverse of an isomorphism of sheaves of modules are bijective. -/
theorem _root_.Stacks.SheafOfModules.bijective_inv_val_app {R' : Sheaf J RingCat.{w}}
    {N₁ N₂ : SheafOfModules.{w} R'} (e : N₁ ≅ N₂) (X : C₁ᵒᵖ) :
    Function.Bijective (e.inv.val.app X) := by
  refine Function.bijective_iff_has_inverse.mpr ⟨e.hom.val.app X, fun y => ?_, fun y => ?_⟩
  · exact congrArg (fun φ : N₂ ⟶ N₂ => φ.val.app X y) e.inv_hom_id
  · exact congrArg (fun φ : N₁ ⟶ N₁ => φ.val.app X y) e.hom_inv_id

/-- The restriction maps of a restricted module. -/
theorem moduleRestriction_obj_map_apply (N : SheafOfModules.{w} R) {X Y : C₁ᵒᵖ} (g : X ⟶ Y)
    (z : ((moduleRestriction J K v R).obj N).val.obj X) :
    ((moduleRestriction J K v R).obj N).val.map g z = N.val.map (v.map g.unop).op z :=
  rfl

/-- A morphism of restricted modules from additive maps on the sections over the subsite which
are natural and linear. -/
noncomputable def restrictionHomOfApply (N₁ N₂ : SheafOfModules.{w} R)
    (f : ∀ X : C₁, N₁.val.obj (op (v.obj X)) →+ N₂.val.obj (op (v.obj X)))
    (nat : ∀ {X Y : C₁} (g : X ⟶ Y) (x : N₁.val.obj (op (v.obj Y))),
      f X (N₁.val.map (v.map g).op x) = N₂.val.map (v.map g).op (f Y x))
    (smul : ∀ (X : C₁) (r : R.val.obj (op (v.obj X))) (m : N₁.val.obj (op (v.obj X))),
      f X (r • m) = r • f X m) :
    (moduleRestriction J K v R).obj N₁ ⟶ (moduleRestriction J K v R).obj N₂ :=
  ⟨Stacks.PresheafOfModules.homOfApply (fun X => f X.unop) (fun g x => nat g.unop x)
    (fun X r m => smul X.unop r m)⟩

/-- The components of `restrictionHomOfApply` on a chart `X` of the subsite are the given additive
maps. -/
theorem restrictionHomOfApply_app (N₁ N₂ : SheafOfModules.{w} R)
    (f : ∀ X : C₁, N₁.val.obj (op (v.obj X)) →+ N₂.val.obj (op (v.obj X)))
    (nat : ∀ {X Y : C₁} (g : X ⟶ Y) (x : N₁.val.obj (op (v.obj Y))),
      f X (N₁.val.map (v.map g).op x) = N₂.val.map (v.map g).op (f Y x))
    (smul : ∀ (X : C₁) (r : R.val.obj (op (v.obj X))) (m : N₁.val.obj (op (v.obj X))),
      f X (r • m) = r • f X m) (X : C₁) (x : N₁.val.obj (op (v.obj X))) :
    (restrictionHomOfApply J K v R N₁ N₂ f nat smul).val.app (op X) x = f X x :=
  rfl

end Stacks.DenseSubsiteModules

namespace AlgebraicGeometry.Stack

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS B)
  (M : Space.QuasicoherentModule C S hS G)

/-- The affine point of `[U/_pR]` given by an affine étale chart of `U`. -/
def affineChartPoint (A : Space.AffineEtale C S hS G.objects.obj) :
    AffineCategory C S hS (presheafOfGroupoids
      (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p :=
  ⟨chartPoint G A.obj, A.property⟩

/-- **The map `𝒢(W) ⟶ ℱ(x(u_W))`** over an affine étale chart `W` of `U`: the chart section
along `u_W`, read in `ℱ` through the two identifications of its construction. -/
def chartModuleMap (A : Space.AffineEtale C S hS G.objects.obj)
    (x : M.F.obj.val.obj (op A.obj)) :
    (quotientStackObjectRestriction G (quotientStackModuleOfGroupoid G M)).val.obj (op A.obj) :=
  ((pointwiseRestriction G).objObjPreimageIso (pointwiseModule G M)).inv.val.app
    (op (chartPoint G A.obj))
    ((pointwiseModuleAffineIso G M).inv.val.app (op (affineChartPoint G A))
      (chartPointSection G M A.obj x))

/-- A function on a chart `W` of `U`, read on the identity chart of `W`. -/
def selfChartScalar (W : Space.SmallEtale C S hS G.objects.obj)
    (r : Space.chartRing C S hS G.objects.obj G.objects.property W) :
    Space.chartRing C S hS (Space.yonedaSpace C S hS (chartPoint G W).base).1
      (Space.yonedaSpace C S hS (chartPoint G W).base).2
      (Space.selfChart C S hS (chartPoint G W).base) := r

/-- A function on an affine chart `W` of `U`, read on the affine point `u_W` of `[U/_pR]`. -/
def affinePointScalar (A : Space.AffineEtale C S hS G.objects.obj)
    (r : Space.chartRing C S hS G.objects.obj G.objects.property A.obj) :
    (Stacks.SheafOfModules.Tensor.ringSheaf (AffineCategory.siteKindRingedSite C S hS
      (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p
      (isFiberedInGroupoids_presheafOfGroupoids _) .fppf).chaotic.O).obj.obj
        (op (affineChartPoint G A)) := r

/-- A function on an affine chart `W` of `U`, read on the point `u_W` of `[U/_pR]`. -/
def pointScalar (A : Space.AffineEtale C S hS G.objects.obj)
    (r : Space.chartRing C S hS G.objects.obj G.objects.property A.obj) :
    (FibredSite.ringStructureSheafCore C S hS (presheafOfGroupoids
      (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p
      (isFiberedInGroupoids_presheafOfGroupoids _) .fppf).obj.obj (op (chartPoint G A.obj)) := r

/-- The chart section along `u_W` commutes with multiplication by functions on `W`. -/
theorem chartPointSection_smul (W : Space.SmallEtale C S hS G.objects.obj)
    (r : Space.chartRing C S hS G.objects.obj G.objects.property W)
    (x : M.F.obj.val.obj (op W)) :
    chartPointSection G M W (r • x) = selfChartScalar G W r • chartPointSection G M W x := by
  refine (Space.modulePullbackChartSection_smul C S hS (pointMap G (chartPoint G W)) M.F.obj
    (pointChartDiagram G (chartPoint G W) W (𝟙 _) (chartPoint_comm G W)) r x).trans ?_
  congr 1

/-- The map `𝒢(W) ⟶ ℱ(x(u_W))` commutes with multiplication by functions on `W`. -/
theorem chartModuleMap_smul (A : Space.AffineEtale C S hS G.objects.obj)
    (r : Space.chartRing C S hS G.objects.obj G.objects.property A.obj)
    (x : M.F.obj.val.obj (op A.obj)) :
    chartModuleMap G M A (r • x) = r • chartModuleMap G M A x := by
  have h2 := ((pointwiseModuleAffineIso G M).inv.val.app (op (affineChartPoint G A))).hom.map_smul
    (affinePointScalar G A r) (chartPointSection G M A.obj x)
  have h3 := (((pointwiseRestriction G).objObjPreimageIso (pointwiseModule G M)).inv.val.app
    (op (chartPoint G A.obj))).hom.map_smul (pointScalar G A r)
    ((pointwiseModuleAffineIso G M).inv.val.app (op (affineChartPoint G A))
      (chartPointSection G M A.obj x))
  unfold chartModuleMap
  rw [chartPointSection_smul]
  exact (congrArg _ h2).trans
    (h3.trans (congrArg (· • _) (quotientStackProj_chartStructureHom_apply G A.obj r).symm))

/-- The arrow of affine points of `[U/_pR]` underlying a morphism of affine étale charts. -/
def affineChartPointHom {A₁ A₂ : Space.AffineEtale C S hS G.objects.obj} (f : A₁ ⟶ A₂) :
    affineChartPoint G A₁ ⟶ affineChartPoint G A₂ :=
  ObjectProperty.homMk (chartPointHom G ((Space.AffineEtale.inclusion C S hS _).map f))

/-- **Naturality of `𝒢(W) ⟶ ℱ(x(u_W))` in the affine chart `W`.** -/
theorem chartModuleMap_naturality {A₁ A₂ : Space.AffineEtale C S hS G.objects.obj} (f : A₁ ⟶ A₂)
    (x : M.F.obj.val.obj (op A₂.obj)) :
    chartModuleMap G M A₁ (M.F.obj.val.map ((Space.AffineEtale.inclusion C S hS _).map f).op x) =
      (quotientStackObjectRestriction G (quotientStackModuleOfGroupoid G M)).val.map
        ((Space.AffineEtale.inclusion C S hS _).map f).op (chartModuleMap G M A₂ x) := by
  have h1 := pointSectionRestrict_chartPointSection G M
    ((Space.AffineEtale.inclusion C S hS _).map f) x
  have := AffineCategory.isDenseSubsite_inclusion_siteKind C S hS (presheafOfGroupoids
    (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p
    (isFiberedInGroupoids_presheafOfGroupoids _) .fppf
  have hp : (pointPresheaf G M).map (affineChartPointHom G f).op (chartPointSection G M A₂.obj x) =
      pointSectionRestrict G M (chartPointHom G ((Space.AffineEtale.inclusion C S hS _).map f))
        (chartPointSection G M A₂.obj x) :=
    (Stacks.PresheafOfModules.mkOfSemilinear_map_apply (fun x => pointModule G M x.unop)
      (fun f => affinePointSemilinear G M f) (affinePointSemilinear_id G M)
      (fun f g s => affinePointSemilinear_comp G M f g s) (affineChartPointHom G f).op
      (chartPointSection G M A₂.obj x)).trans
    (affinePointSemilinear_apply G M (affineChartPointHom G f).op (chartPointSection G M A₂.obj x))
  have h2₀ := PresheafOfModules.naturality_apply (pointwiseModuleAffineIso G M).inv.val
    (affineChartPointHom G f).op (chartPointSection G M A₂.obj x)
  have h2 := (congrArg ((pointwiseModuleAffineIso G M).inv.val.app (op (affineChartPoint G A₁)))
    hp.symm).trans (h2₀.trans (Stacks.DenseSubsiteModules.moduleRestriction_obj_map_apply _ _ _ _
      (pointwiseModule G M) (affineChartPointHom G f).op
      ((pointwiseModuleAffineIso G M).inv.val.app (op (affineChartPoint G A₂))
        (chartPointSection G M A₂.obj x))))
  have h3 := PresheafOfModules.naturality_apply
    ((pointwiseRestriction G).objObjPreimageIso (pointwiseModule G M)).inv.val
    (chartPointHom G ((Space.AffineEtale.inclusion C S hS _).map f)).op
    ((pointwiseModuleAffineIso G M).inv.val.app (op (affineChartPoint G A₂))
      (chartPointSection G M A₂.obj x))
  unfold chartModuleMap
  refine (congrArg (fun y => ((pointwiseRestriction G).objObjPreimageIso
    (pointwiseModule G M)).inv.val.app (op (chartPoint G A₁.obj))
      ((pointwiseModuleAffineIso G M).inv.val.app (op (affineChartPoint G A₁)) y)) h1.symm).trans ?_
  refine (congrArg (((pointwiseRestriction G).objObjPreimageIso
    (pointwiseModule G M)).inv.val.app (op (chartPoint G A₁.obj))) h2).trans ?_
  exact h3

/-- The chart section along `u_W` is additive. -/
theorem chartPointSection_add (W : Space.SmallEtale C S hS G.objects.obj)
    (x y : M.F.obj.val.obj (op W)) :
    chartPointSection G M W (x + y) = chartPointSection G M W x + chartPointSection G M W y :=
  Space.modulePullbackChartSection_add C S hS (pointMap G (chartPoint G W)) M.F.obj
    (pointChartDiagram G (chartPoint G W) W (𝟙 _) (chartPoint_comm G W)) x y

/-- The map `𝒢(W) ⟶ ℱ(x(u_W))` is additive. -/
theorem chartModuleMap_add (A : Space.AffineEtale C S hS G.objects.obj)
    (x y : M.F.obj.val.obj (op A.obj)) :
    chartModuleMap G M A (x + y) = chartModuleMap G M A x + chartModuleMap G M A y := by
  unfold chartModuleMap
  rw [chartPointSection_add]
  exact (congrArg _ (map_add _ _ _)).trans (map_add _ _ _)

/-- **`𝒢(W) ⟶ ℱ(x(u_W))` is bijective** on affine charts. -/
theorem bijective_chartModuleMap (A : Space.AffineEtale C S hS G.objects.obj) :
    Function.Bijective (chartModuleMap G M A) :=
  (Stacks.SheafOfModules.bijective_inv_val_app _
    ((pointwiseRestriction G).objObjPreimageIso (pointwiseModule G M)) _).comp
    ((Stacks.SheafOfModules.bijective_inv_val_app _ (pointwiseModuleAffineIso G M) _).comp
      (bijective_chartPointSection G M A.obj A.property))

/-- The affine étale charts of `U` form a dense subsite of the small étale site of `U`. -/
instance : (Space.AffineEtale.inclusion C S hS G.objects.obj).IsDenseSubsite
    (Space.AffineEtale.topology C S hS G.objects.obj)
    (Space.SmallEtale.topology C S hS G.objects.obj) :=
  (Space.AffineEtale.inclusion_isSpecialCocontinuous C S hS _ G.objects.property).2

/-- Restriction of `𝒪_U`-modules to the affine étale charts of `U` (Stacks 04JS). -/
abbrev affineChartRestriction :=
  Stacks.DenseSubsiteModules.moduleRestriction (Space.AffineEtale.topology C S hS G.objects.obj)
    (Space.SmallEtale.topology C S hS G.objects.obj) (Space.AffineEtale.inclusion C S hS _)
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (Space.smallEtaleRingedSite C S hS G.objects.obj G.objects.property).O)

/-- `𝒢(W) ⟶ ℱ(x(u_W))` as an additive map. -/
def chartModuleAddHom (A : Space.AffineEtale C S hS G.objects.obj) :
    M.F.obj.val.obj (op A.obj) →+
      (quotientStackObjectRestriction G (quotientStackModuleOfGroupoid G M)).val.obj (op A.obj) :=
  AddMonoidHom.mk' (chartModuleMap G M A) (chartModuleMap_add G M A)

/-- The additive map `chartModuleAddHom` is `chartModuleMap`. -/
theorem chartModuleAddHom_apply (A : Space.AffineEtale C S hS G.objects.obj)
    (x : M.F.obj.val.obj (op A.obj)) : chartModuleAddHom G M A x = chartModuleMap G M A x :=
  rfl

/-- **The morphism `𝒢 ⟶ x^*ℱ|_{U_étale}` on the affine étale charts of `U`.** -/
def affineChartModuleHom :
    (affineChartRestriction G).obj M.F.obj ⟶
      (affineChartRestriction G).obj
        (quotientStackObjectRestriction G (quotientStackModuleOfGroupoid G M)) :=
  Stacks.DenseSubsiteModules.restrictionHomOfApply _ _ _ _ _ _
    (fun A => chartModuleAddHom G M A) (fun f x => chartModuleMap_naturality G M f x)
    (fun A r x => chartModuleMap_smul G M A r x)

/-- The component of `affineChartModuleHom` at an affine chart `W` is `chartModuleMap`. -/
theorem affineChartModuleHom_app (A : Space.AffineEtale C S hS G.objects.obj)
    (x : M.F.obj.val.obj (op A.obj)) :
    (affineChartModuleHom G M).val.app (op A) x = chartModuleMap G M A x :=
  rfl

/-- The morphism `affineChartModuleHom` is an isomorphism. -/
instance : IsIso (affineChartModuleHom G M) :=
  Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_isIso_val_app _ fun A =>
    (ConcreteCategory.isIso_iff_bijective _).mpr (bijective_chartModuleMap G M A.unop)

/-- **The morphism `𝒢 ⟶ x^*ℱ|_{U_étale}`**, glued from the affine charts of `U`. -/
def quotientStackModuleOfGroupoidHom :
    M.F.obj ⟶ quotientStackObjectRestriction G (quotientStackModuleOfGroupoid G M) :=
  (affineChartRestriction G).preimage (affineChartModuleHom G M)

/-- **`𝒢 ⟶ x^*ℱ|_{U_étale}` is an isomorphism.** -/
instance isIso_quotientStackModuleOfGroupoidHom :
    IsIso (quotientStackModuleOfGroupoidHom G M) := by
  have h : (affineChartRestriction G).map (quotientStackModuleOfGroupoidHom G M) =
      affineChartModuleHom G M := Functor.map_preimage _ _
  haveI : IsIso ((affineChartRestriction G).map (quotientStackModuleOfGroupoidHom G M)) := by
    rw [h]
    infer_instance
  exact isIso_of_fully_faithful (affineChartRestriction G) _

/-- The values of `𝒢 ⟶ x^*ℱ|_{U_étale}` on affine charts. -/
theorem quotientStackModuleOfGroupoidHom_app (A : Space.AffineEtale C S hS G.objects.obj)
    (x : M.F.obj.val.obj (op A.obj)) :
    (quotientStackModuleOfGroupoidHom G M).val.app (op A.obj) x = chartModuleMap G M A x :=
  congrArg (fun φ => φ.val.app (op A) x) (Functor.map_preimage (affineChartRestriction G)
    (affineChartModuleHom G M))

end AlgebraicGeometry.Stack

end
