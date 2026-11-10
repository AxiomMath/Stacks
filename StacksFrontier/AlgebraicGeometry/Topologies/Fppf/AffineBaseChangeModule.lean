module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.Additive
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcHomSheafRefinement
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde
public import StacksFrontier.AlgebraicGeometry.Topologies.BigFppfStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.OverSliceContinuity
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Equivalence
public import StacksFrontier.AlgebraicGeometry.Topologies.SiteStructureSheaf
public import StacksCore.Tactic.StacksAttribute

/-!
# The base-change module on the big affine fppf site of an affine scheme

Let `S = Spec A` be an affine scheme and let `M` be an `A`-module. The rule
`(U/S) = (Spec B/Spec A) ↦ M ⊗_A B` is a presheaf of `𝒪`-modules on `(Aff/S)_fppf`, and it is
in fact a sheaf: it is the associated module `(M̃)^a` of Tag 03DU restricted to the affine
objects.

## Main definitions

* `AlgebraicGeometry.BigAffineFppf.coordinateAlgebra` is the presheaf of `A`-algebras
  `U ↦ Γ(U, 𝒪_U)` on `(Aff/S)_fppf`.
* `AlgebraicGeometry.BigAffineFppf.baseChangePresheaf` is the rule `U ↦ M ⊗_A Γ(U, 𝒪_U)` and
  `AlgebraicGeometry.BigAffineFppf.baseChangeModule` upgrades it to a presheaf of `𝒪`-modules.
* `AlgebraicGeometry.BigAffineFppf.baseChangeSheafFunctor` is the resulting functor from
  `A`-modules to sheaves of `𝒪`-modules, and
  `AlgebraicGeometry.BigAffineFppf.baseChangeComplex` its termwise extension to complexes.
* `AlgebraicGeometry.BigAffineFppf.baseChangePresheafIso` identifies `U ↦ M ⊗_A Γ(U, 𝒪_U)` with
  the associated module of `M̃` on this site.

## Main results

* `AlgebraicGeometry.BigAffineFppf.structurePresheaf_isSheaf`: the presheaf of global functions
  is a sheaf of rings on `(Aff/S)_fppf`.
* `AlgebraicGeometry.BigAffineFppf.baseChangePresheaf_isSheaf`: each `U ↦ M ⊗_A Γ(U, 𝒪_U)` is a
  sheaf, so a complex of `A`-modules gives a complex of modules and not merely of presheaves of
  modules.

## Implementation notes

The base change `M ⊗_A B` is written as `TensorProduct A (Γ(U, 𝒪_U)) M`, the order for which
the `Γ(U, 𝒪_U)`-module structure on the tensor product is the library's. Objects of
`(Aff/S)_fppf` are not assumed presented as `Spec B`: the rule uses the coordinate ring
`Γ(U, 𝒪_U)`, which is `B` when `U = Spec B`.

The sheaf condition is Tag 03DT, the fpqc sheaf condition for the pullback-sections presheaf of
a quasi-coherent module, restricted along the canonical functor of the site:
`Stacks.Sites.isSheaf_associatedPresheaf_of_isContinuous` applied to `M̃`, together with the
identification `M ⊗_A Γ(U, 𝒪_U) ≅ Γ(U, U.hom⁺ M̃)`, which is an isomorphism because the objects
of this site are affine — the affine base change of Tag 01I9.

## References

* [Stacks Project, Tag 0H0U](https://stacks.math.columbia.edu/tag/0H0U)
* [Stacks Project, Tag 03DT](https://stacks.math.columbia.edu/tag/03DT)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe u

namespace AlgebraicGeometry.BigAffineFppf

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (A : CommRingCat.{u})
  (hS : B.Contains (Spec A))

/-! ### The big affine fppf site of an affine scheme -/

/-- The fppf topology on `(Aff/Spec A)_fppf`. -/
public abbrev affineTopology : GrothendieckTopology (BigAffineFppf B (Spec A) hS) :=
  BigAffineFppf.topology B (Spec A) hS

/-- An object of `(Aff/Spec A)_fppf`, viewed as a scheme over `Spec A`. -/
public abbrev toOver : BigAffineFppf B (Spec A) hS ⥤ Over (Spec A) :=
  BigAffineFppf.inclusion B (Spec A) hS ⋙ Over.post B.inclusion

/-- The presheaf of coordinate rings `U ↦ Γ(U, 𝒪_U)` on `(Aff/Spec A)_fppf`. -/
public abbrev coordinateRing : (BigAffineFppf B (Spec A) hS)ᵒᵖ ⥤ CommRingCat.{u} :=
  (toOver B A hS ⋙ Over.forget (Spec A)).op ⋙ Scheme.Γ

/-- The structure morphism of an object of `(Aff/Spec A)_fppf` makes its coordinate ring an
`A`-algebra. -/
public def structureAlgebraMap (X : (BigAffineFppf B (Spec A) hS)ᵒᵖ) :
    A ⟶ (coordinateRing B A hS).obj X :=
  (Scheme.ΓSpecIso A).inv ≫ ((toOver B A hS).obj X.unop).hom.appTop

/-- The restriction maps of the coordinate rings are maps of `A`-algebras. -/
public theorem structureAlgebraMap_naturality {X Y : (BigAffineFppf B (Spec A) hS)ᵒᵖ}
    (φ : X ⟶ Y) :
    structureAlgebraMap B A hS X ≫ (coordinateRing B A hS).map φ =
      structureAlgebraMap B A hS Y := by
  have h : ((toOver B A hS).obj X.unop).hom.appTop ≫
      ((toOver B A hS).map φ.unop).left.appTop =
      ((toOver B A hS).obj Y.unop).hom.appTop := by
    rw [← Scheme.Hom.comp_appTop, Over.w]
  change (Scheme.ΓSpecIso A).inv ≫ ((toOver B A hS).obj X.unop).hom.appTop ≫
      ((toOver B A hS).map φ.unop).left.appTop =
    (Scheme.ΓSpecIso A).inv ≫ ((toOver B A hS).obj Y.unop).hom.appTop
  rw [h]

/-- The coordinate rings of `(Aff/Spec A)_fppf` as `A`-algebras, functorially. -/
public def coordinateAlgebra : (BigAffineFppf B (Spec A) hS)ᵒᵖ ⥤ Under A where
  obj X := Under.mk (structureAlgebraMap B A hS X)
  map φ := Under.homMk ((coordinateRing B A hS).map φ)
    (structureAlgebraMap_naturality B A hS φ)

/-! ### The base-change presheaf -/

private theorem tensorAddHom_ext {R M N P : Type u} [CommRing R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] [AddCommGroup P]
    {f g : TensorProduct R M N →+ P}
    (h : ∀ (m : M) (n : N), f (m ⊗ₜ[R] n) = g (m ⊗ₜ[R] n)) : f = g := by
  refine AddMonoidHom.ext fun x => ?_
  induction x using TensorProduct.inductionOn with
  | tmul m n => exact h m n
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- Base change of a fixed `A`-module along an `A`-algebra, `B ⊗_A M`, functorially in the
`A`-algebra. -/
public def baseChangeUnder (M : ModuleCat.{u} A) : Under A ⥤ AddCommGrpCat.{u} where
  obj U := AddCommGrpCat.of (TensorProduct A U M)
  map f := AddCommGrpCat.ofHom
    (TensorProduct.map (CommRingCat.toAlgHom f).toLinearMap LinearMap.id).toAddMonoidHom
  map_id U := by exact AddCommGrpCat.hom_ext <| tensorAddHom_ext fun _ _ => rfl
  map_comp f g := by exact AddCommGrpCat.hom_ext <| tensorAddHom_ext fun _ _ => rfl

/-- Base change of a map of `A`-modules. -/
public def baseChangeUnderMap {M N : ModuleCat.{u} A} (f : M ⟶ N) :
    baseChangeUnder A M ⟶ baseChangeUnder A N where
  app U := AddCommGrpCat.ofHom
    (TensorProduct.map (LinearMap.id (R := A) (M := U)) f.hom).toAddMonoidHom
  naturality U V g := by exact AddCommGrpCat.hom_ext <| tensorAddHom_ext fun _ _ => rfl

/-- **Stacks 0H0U.** The rule `(U/S) = (Spec B/Spec A) ↦ M ⊗_A B`, as a presheaf of abelian
groups on `(Aff/Spec A)_fppf`. -/
public abbrev baseChangePresheaf (M : ModuleCat.{u} A) :
    (BigAffineFppf B (Spec A) hS)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  coordinateAlgebra B A hS ⋙ baseChangeUnder A M

/-- The rule `U ↦ M ⊗_A Γ(U, 𝒪_U)`, as a functor of the `A`-module. -/
public def baseChangePresheafFunctor : ModuleCat.{u} A ⥤
    ((BigAffineFppf B (Spec A) hS)ᵒᵖ ⥤ AddCommGrpCat.{u}) where
  obj M := baseChangePresheaf B A hS M
  map f := Functor.whiskerLeft (coordinateAlgebra B A hS) (baseChangeUnderMap A f)
  map_id M := by
    exact NatTrans.ext <| funext fun _ =>
      AddCommGrpCat.hom_ext <| tensorAddHom_ext fun _ _ => rfl
  map_comp f g := by
    exact NatTrans.ext <| funext fun _ =>
      AddCommGrpCat.hom_ext <| tensorAddHom_ext fun _ _ => rfl

/-- Base change of `A`-modules is additive in the module. -/
public instance baseChangePresheafFunctor_additive :
    (baseChangePresheafFunctor B A hS).Additive where
  map_add {_ _} f g := NatTrans.ext <| funext fun _ => AddCommGrpCat.hom_ext <|
    tensorAddHom_ext fun b m => TensorProduct.tmul_add b (f.hom m) (g.hom m)

/-- The coordinate ring of `U` acts on the base change of `M` to it. -/
@[instance_reducible]
public def baseChangePresheafModule (M : ModuleCat.{u} A)
    (X : (BigAffineFppf B (Spec A) hS)ᵒᵖ) :
    Module ((Stacks.Sites.structurePresheaf (Spec A) (toOver B A hS)).obj X)
      ((baseChangePresheaf B A hS M).obj X) :=
  inferInstanceAs (Module ((coordinateAlgebra B A hS).obj X)
    (TensorProduct A ((coordinateAlgebra B A hS).obj X) M))

attribute [instance] baseChangePresheafModule

/-- **Stacks 0H0U.** Restriction in the base-change presheaf is semilinear over restriction of
functions: the rule `U ↦ M ⊗_A Γ(U, 𝒪_U)` is a presheaf of `𝒪`-modules. -/
@[stacks 0H0U "the rule is a presheaf of modules"]
public theorem baseChangePresheaf_map_smul (M : ModuleCat.{u} A)
    ⦃X Y : (BigAffineFppf B (Spec A) hS)ᵒᵖ⦄ (φ : X ⟶ Y)
    (r : (Stacks.Sites.structurePresheaf (Spec A) (toOver B A hS)).obj X)
    (m : (baseChangePresheaf B A hS M).obj X) :
    (baseChangePresheaf B A hS M).map φ (r • m) =
        (Stacks.Sites.structurePresheaf (Spec A) (toOver B A hS)).map φ r •
        (baseChangePresheaf B A hS M).map φ m := by
  let R := (coordinateAlgebra B A hS).obj X
  let T := (coordinateAlgebra B A hS).obj Y
  let _ : Module R.right ((baseChangePresheaf B A hS M).obj X) :=
    baseChangePresheafModule B A hS M X
  let _ : Module T.right ((baseChangePresheaf B A hS M).obj Y) :=
    baseChangePresheafModule B A hS M Y
  let _ : Module R.right (TensorProduct A R M) := inferInstance
  let _ : Module T.right (TensorProduct A T M) := inferInstance
  let f := CommRingCat.toAlgHom ((coordinateAlgebra B A hS).map φ)
  let r' : R.right := r
  change (TensorProduct.map f.toLinearMap LinearMap.id)
      (r' • (m : TensorProduct A R M)) =
    f r' • (TensorProduct.map f.toLinearMap LinearMap.id) (m : TensorProduct A R M)
  induction m using TensorProduct.inductionOn with
  | tmul b m =>
      change (TensorProduct.map f.toLinearMap LinearMap.id)
          (r' • (b ⊗ₜ[A] m)) =
        f r' • (TensorProduct.map f.toLinearMap LinearMap.id) (b ⊗ₜ[A] m)
      rw [TensorProduct.smul_tmul', TensorProduct.map_tmul,
        TensorProduct.map_tmul, TensorProduct.smul_tmul']
      simp [map_mul]
  | add x y hx hy =>
      change (TensorProduct.map f.toLinearMap LinearMap.id) (r' • (x + y)) =
        f r' • (TensorProduct.map f.toLinearMap LinearMap.id) (x + y)
      simp only [map_add, smul_add]
      exact congrArg₂ (· + ·) hx hy

/-- Base change of a map of `A`-modules, on sections over an `A`-algebra. -/
public abbrev baseChangeTensorMap {M N : ModuleCat.{u} A} (f : M ⟶ N) (U : Under A) :
    TensorProduct A U M →ₗ[A] TensorProduct A U N :=
  TensorProduct.map (LinearMap.id (R := A) (M := U)) f.hom

/-- Base change of a map of `A`-modules is linear over the coordinate rings, which makes the
rule `U ↦ M ⊗_A Γ(U, 𝒪_U)` functorial in `M`. -/
public theorem baseChangeTensorMap_smul {M N : ModuleCat.{u} A} (f : M ⟶ N)
    (U : Under A) (r : U) (m : TensorProduct A U M) :
    baseChangeTensorMap A f U (r • m) = r • baseChangeTensorMap A f U m := by
  refine DFunLike.congr_fun (tensorAddHom_ext
    (f := (baseChangeTensorMap A f U).toAddMonoidHom.comp (DistribSMul.toAddMonoidHom _ r))
    (g := (DistribSMul.toAddMonoidHom _ r).comp (baseChangeTensorMap A f U).toAddMonoidHom)
    fun b m => ?_) m
  simp [baseChangeTensorMap, TensorProduct.smul_tmul', TensorProduct.map_tmul]

/-- The base change `U ↦ M ⊗_A Γ(U, 𝒪_U)` as a presheaf of `𝒪`-modules. -/
public def baseChangeModule (M : ModuleCat.{u} A) :
    PresheafOfModules.{u} (Stacks.Sites.structurePresheaf (Spec A) (toOver B A hS)) :=
  PresheafOfModules.ofPresheaf (baseChangePresheaf B A hS M)
    (baseChangePresheaf_map_smul B A hS M)

/-- The underlying presheaf of abelian groups of
`AlgebraicGeometry.BigAffineFppf.baseChangeModule` is the rule `U ↦ M ⊗_A Γ(U, 𝒪_U)`. -/
@[simp] public theorem baseChangeModule_presheaf (M : ModuleCat.{u} A) :
    (baseChangeModule B A hS M).presheaf = baseChangePresheaf B A hS M :=
  PresheafOfModules.ofPresheaf_presheaf _ _

private theorem baseChangePresheafFunctor_app_congr {M N : ModuleCat.{u} A}
    {τ σ : (baseChangePresheafFunctor B A hS).obj M ⟶
      (baseChangePresheafFunctor B A hS).obj N}
    (h : τ = σ) (X : (BigAffineFppf B (Spec A) hS)ᵒᵖ)
    (x : (baseChangePresheaf B A hS M).obj X) : τ.app X x = σ.app X x := by
  rw [h]

/-- Base change as a functor from `A`-modules to presheaves of `𝒪`-modules on
`(Aff/Spec A)_fppf`. -/
public def baseChangeModuleFunctor : ModuleCat.{u} A ⥤
    PresheafOfModules.{u} (Stacks.Sites.structurePresheaf (Spec A) (toOver B A hS)) where
  obj M := baseChangeModule B A hS M
  map f := PresheafOfModules.homMk ((baseChangePresheafFunctor B A hS).map f)
    (fun X r m => baseChangeTensorMap_smul A f ((coordinateAlgebra B A hS).obj X) r m)
  map_id M := by
    exact PresheafOfModules.hom_ext fun X => ModuleCat.hom_ext <| LinearMap.ext fun x =>
      baseChangePresheafFunctor_app_congr B A hS
        ((baseChangePresheafFunctor B A hS).map_id M) X x
  map_comp f g := by
    exact PresheafOfModules.hom_ext fun X => ModuleCat.hom_ext <| LinearMap.ext fun x =>
      baseChangePresheafFunctor_app_congr B A hS
        ((baseChangePresheafFunctor B A hS).map_comp f g) X x

/-- Base change is additive, so it extends termwise to complexes. -/
public instance baseChangeModuleFunctor_additive :
    (baseChangeModuleFunctor B A hS).Additive where
  map_add {_ _} f g :=
    PresheafOfModules.hom_ext fun X => ModuleCat.hom_ext <| LinearMap.ext fun x =>
      baseChangePresheafFunctor_app_congr B A hS
        ((baseChangePresheafFunctor B A hS).map_add (f := f) (g := g)) X x

/-! ### The sheaf conditions -/

/-- The canonical functor of `(Aff/Spec A)_fppf` into the schemes over `Spec A` is continuous
for the localized fpqc topology: the inclusion of the affine objects into the big fppf site is
a dense subsite, hence continuous, and the canonical functor of the big fppf site is continuous
for the fpqc topology. -/
public instance isContinuous_toOver :
    (toOver B A hS).IsContinuous (affineTopology B A hS)
      (Scheme.fpqcTopology.{u}.over (Spec A)) := by
  let _ : (BigAffineFppf.inclusion B (Spec A) hS).IsDenseSubsite
      (affineTopology B A hS) (BigFppfOver.topology B (Spec A) hS) :=
    bigAffineFppfInclusion_isDenseSubsite B (Spec A) hS
  let _ : (Over.post B.inclusion : BigFppfOver B (Spec A) hS ⥤ Over (Spec A)).IsContinuous
      (BigFppfOver.topology B (Spec A) hS) (Scheme.fpqcTopology.{u}.over (Spec A)) :=
    AlgebraicGeometry.isContinuous_overToSlice_fpqc CoveringTopology.fppf B (Spec A) hS
  exact Functor.isContinuous_comp (BigAffineFppf.inclusion B (Spec A) hS)
    (Over.post B.inclusion) (affineTopology B A hS)
    (BigFppfOver.topology B (Spec A) hS) (Scheme.fpqcTopology.{u}.over (Spec A))

/-- The presheaf of global functions is a sheaf of rings on `(Aff/Spec A)_fppf`: global
functions are an fpqc sheaf on the schemes over `Spec A`, and the canonical functor of the site
is continuous for the fpqc topology. -/
public theorem structurePresheaf_isSheaf :
    Presheaf.IsSheaf (affineTopology B A hS)
      (Stacks.Sites.structurePresheaf (Spec A) (toOver B A hS)) :=
  Stacks.Sites.isSheaf_structurePresheaf (Spec A) _ (toOver B A hS)
    ((toOver B A hS).op_comp_isSheaf _ _
      ⟨Stacks.Sites.globalSectionsOver (Spec A),
        Stacks.Sites.isSheaf_fpqcOver_globalSections (Spec A)⟩)


/-! ### Identification with the associated module -/

open scoped ChangeOfRings

/-- The coordinate rings of the schemes over `Spec A` as `A`-algebras. -/
private def overCoordinateAlgebra : (Over (Spec A))ᵒᵖ ⥤ Under A where
  obj X := Under.mk ((Scheme.ΓSpecIso A).inv ≫ X.unop.hom.appTop)
  map {X Y} f := Under.homMk f.unop.left.appTop (by
    change (Scheme.ΓSpecIso A).inv ≫ X.unop.hom.appTop ≫ f.unop.left.appTop = _
    rw [← Scheme.Hom.comp_appTop, Over.w]
    rfl)
  map_id X := by
    ext1
    exact Scheme.Hom.id_appTop
  map_comp f g := by
    ext1
    exact Scheme.Hom.comp_appTop _ _

/-- The canonical map `M ⟶ Γ(X, X.hom⁺ M̃)`, the unit of pullback-pushforward on the global
sections of the sheaf associated to `M`. -/
private def pullbackSectionUnit (M : ModuleCat A) (X : Over (Spec A)) :
    M →+ Γ((Scheme.Modules.pullback X.hom).obj (tilde M), ⊤) :=
  (Scheme.Modules.Hom.app
    ((Scheme.Modules.pullbackPushforwardAdjunction X.hom).unit.app (tilde M)) ⊤).hom.comp
    (tilde.toOpen M ⊤).hom.toAddMonoidHom

lemma map_leTop_top {X : Scheme.{u}} (z : Γ(X, ⊤)) :
    (X.presheaf.map ((⊤ : X.Opens).leTop).op) z = z := by
  have h : (X.presheaf.map ((⊤ : X.Opens).leTop).op) = 𝟙 _ :=
    Eq.trans (congrArg X.presheaf.map (Subsingleton.elim _ (𝟙 (op (⊤ : X.Opens)))))
      (X.presheaf.map_id _)
  rw [h]
  rfl

private lemma pullbackSectionUnit_smul (M : ModuleCat A) (X : Over (Spec A))
    (a : A) (m : M) :
    pullbackSectionUnit A M X (a • m) =
      ((Scheme.ΓSpecIso A).inv ≫ X.hom.appTop) a • pullbackSectionUnit A M X m := by
  have hsm : (tilde.toOpen M ⊤) (a • m) = a • ((tilde.toOpen M ⊤) m) :=
    (tilde.toOpen M ⊤).hom.map_smul a m
  have hscalar : X.hom.appTop
      (((Spec A).presheaf.map ((⊤ : (Spec A).Opens).leTop).op) ((Scheme.ΓSpecIso A).inv a)) =
      ((Scheme.ΓSpecIso A).inv ≫ X.hom.appTop) a :=
    congrArg (fun z => X.hom.appTop z) (map_leTop_top ((Scheme.ΓSpecIso A).inv a))
  have key := Scheme.Modules.Hom.app_smul
    ((Scheme.Modules.pullbackPushforwardAdjunction X.hom).unit.app (tilde M))
    (((Spec A).presheaf.map ((⊤ : (Spec A).Opens).leTop).op) ((Scheme.ΓSpecIso A).inv a))
    ((tilde.toOpen M ⊤) m)
  refine Eq.trans ?_
    (congrArg (fun s : Γ(X.left, ⊤) => s • pullbackSectionUnit A M X m) hscalar)
  refine Eq.trans (congrArg (fun z => Scheme.Modules.Hom.app
    ((Scheme.Modules.pullbackPushforwardAdjunction X.hom).unit.app (tilde M)) ⊤ z) hsm) ?_
  exact key

private instance pullbackSectionModule (X : Over (Spec A)) (M : ModuleCat A) :
    Module ((overCoordinateAlgebra A).obj (op X))
      Γ((Scheme.Modules.pullback X.hom).obj (tilde M), ⊤) :=
  inferInstanceAs (Module Γ(X.left, ⊤) Γ((Scheme.Modules.pullback X.hom).obj (tilde M), ⊤))

/-- The canonical map `Γ(X, 𝒪) ⊗_A M ⟶ Γ(X, X.hom⁺ M̃)`, `b ⊗ m ↦ b • m|_X`. -/
private def tensorPullbackSections (M : ModuleCat A) (X : Over (Spec A)) :
    TensorProduct A ((overCoordinateAlgebra A).obj (op X)) M →+
      Γ((Scheme.Modules.pullback X.hom).obj (tilde M), ⊤) :=
  TensorProduct.liftAddHom
    { toFun := fun b => b • pullbackSectionUnit A M X
      map_zero' := zero_smul _ _
      map_add' := fun b c => add_smul b c _ }
    (by
      intro a b m
      calc (a • b) • pullbackSectionUnit A M X m
          = ((algebraMap A ((overCoordinateAlgebra A).obj (op X)) a) * b) •
              pullbackSectionUnit A M X m := rfl
        _ = (b * (algebraMap A ((overCoordinateAlgebra A).obj (op X)) a)) •
              pullbackSectionUnit A M X m := by rw [mul_comm]
        _ = b • ((algebraMap A ((overCoordinateAlgebra A).obj (op X)) a) •
              pullbackSectionUnit A M X m) := mul_smul _ _ _
        _ = b • pullbackSectionUnit A M X (a • m) :=
          congrArg (fun z => b • z) (pullbackSectionUnit_smul A M X a m).symm)

private lemma tensorPullbackSections_tmul (M : ModuleCat A) (X : Over (Spec A))
    (b : (overCoordinateAlgebra A).obj (op X)) (m : M) :
    tensorPullbackSections A M X (b ⊗ₜ[A] m) = b • pullbackSectionUnit A M X m := rfl

private lemma pullbackSectionUnit_comp (M : ModuleCat A)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Spec A) (m : M) :
    (((Scheme.Modules.pullbackComp f g).hom.app (tilde M)).app ⊤)
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
        ((Scheme.Modules.pullback g).obj (tilde M))).app ⊤
          (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app (tilde M)).app ⊤
            (tilde.toOpen M ⊤ m))) =
    ((Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).unit.app (tilde M)).app ⊤
      (tilde.toOpen M ⊤ m) := by
  have h := AlgebraicGeometry.pullbackComp_unit f g (tilde M)
  have h' := congrArg (fun k => (k.app ⊤) (tilde.toOpen M ⊤ m)) h
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app,
    Scheme.Modules.pushforwardComp_hom_app_app] at h'
  change (((Scheme.Modules.pullbackComp f g).inv.app (tilde M)).app ⊤)
      (((Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).unit.app (tilde M)).app ⊤
        (tilde.toOpen M ⊤ m)) =
    (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
      ((Scheme.Modules.pullback g).obj (tilde M))).app ⊤
        (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app (tilde M)).app ⊤
          (tilde.toOpen M ⊤ m))) at h'
  rw [← h']
  have hh : ((Scheme.Modules.pullbackComp f g).inv.app (tilde M)).app ⊤ ≫
      ((Scheme.Modules.pullbackComp f g).hom.app (tilde M)).app ⊤ = 𝟙 _ := by
    rw [← Scheme.Modules.Hom.comp_app, Iso.inv_hom_id_app, Scheme.Modules.Hom.id_app]
  exact congrArg (fun k => k
    (((Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).unit.app (tilde M)).app ⊤
      (tilde.toOpen M ⊤ m))) hh

private lemma pullbackSectionUnit_congr (M : ModuleCat A)
    {X : Scheme.{u}} {f g : X ⟶ Spec A} (h : f = g) (m : M) :
    (((Scheme.Modules.pullbackCongr h).hom.app (tilde M)).app ⊤)
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (tilde M)).app ⊤
        (tilde.toOpen M ⊤ m)) =
    ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app (tilde M)).app ⊤
      (tilde.toOpen M ⊤ m) := by
  subst h
  rfl

private lemma pullbackSectionUnit_naturality (M : ModuleCat A)
    {X Y : Over (Spec A)} (g : X ⟶ Y) (m : M) :
    pullbackSectionsMap (tilde M) g (pullbackSectionUnit A M Y m) =
      pullbackSectionUnit A M X m := by
  have h := pullbackSectionUnit_comp A M g.left Y.hom m
  have hunfold : pullbackSectionsMap (tilde M) g =
      ((Scheme.Modules.pullbackPushforwardAdjunction g.left).unit.app
          ((Scheme.Modules.pullback Y.hom).obj (tilde M)) ≫
        (Scheme.Modules.pushforward g.left).map
          ((Scheme.Modules.pullbackComp g.left Y.hom).hom.app (tilde M) ≫
            (Scheme.Modules.pullbackCongr (Over.w g)).hom.app (tilde M))).app ⊤ ≫
      ((Scheme.Modules.pullback X.hom).obj (tilde M)).presheaf.map
        (eqToHom (show (⊤ : X.left.Opens) = g.left ⁻¹ᵁ ⊤ by simp)).op := rfl
  rw [hunfold, Scheme.Modules.presheaf_map_top_eq_id g.left _
    ((Scheme.Modules.pullback X.hom).obj (tilde M))]
  change (((Scheme.Modules.pullbackCongr (Over.w g)).hom.app (tilde M)).app ⊤)
      ((((Scheme.Modules.pullbackComp g.left Y.hom).hom.app (tilde M)).app ⊤)
        (((Scheme.Modules.pullbackPushforwardAdjunction g.left).unit.app
          ((Scheme.Modules.pullback Y.hom).obj (tilde M))).app ⊤
            (((Scheme.Modules.pullbackPushforwardAdjunction Y.hom).unit.app (tilde M)).app ⊤
              (tilde.toOpen M ⊤ m)))) = _
  rw [h]
  exact pullbackSectionUnit_congr A M (Over.w g) m

private lemma tensorPullbackSections_smul (M : ModuleCat A) (X : Over (Spec A))
    (b : (overCoordinateAlgebra A).obj (op X))
    (t : TensorProduct A ((overCoordinateAlgebra A).obj (op X)) M) :
    tensorPullbackSections A M X (b • t) = b • tensorPullbackSections A M X t := by
  refine DFunLike.congr_fun (tensorAddHom_ext
    (f := (tensorPullbackSections A M X).comp (DistribSMul.toAddMonoidHom _ b))
    (g := (DistribSMul.toAddMonoidHom _ b).comp (tensorPullbackSections A M X))
    fun c m => ?_) t
  simp [TensorProduct.smul_tmul', tensorPullbackSections_tmul, mul_smul]

private def specCoordinateLinearEquiv (C : CommRingCat.{u}) (f : A ⟶ C) :
    ((overCoordinateAlgebra A).obj (op (Over.mk (Spec.map f)))) ≃ₗ[A]
      (Under.mk f : Under A) :=
  { __ := ((Scheme.ΓSpecIso C).commRingCatIsoToRingEquiv).toAddEquiv
    map_smul' := by
      intro a b
      change Γ(Spec C, ⊤) at b
      change (Scheme.ΓSpecIso C).hom
        (((Scheme.ΓSpecIso A).inv ≫ (Spec.map f).appTop) a * b) =
          f a * (Scheme.ΓSpecIso C).hom b
      rw [map_mul]
      congr 1
      have h : (Scheme.ΓSpecIso A).inv ≫ (Spec.map f).appTop ≫
          (Scheme.ΓSpecIso C).hom = f := by
        rw [← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
        simp
      exact congrArg (fun k => k a) h }

private def tensorSpecCoordinateEquiv (C : CommRingCat.{u}) (f : A ⟶ C)
    (M : ModuleCat A) :
    TensorProduct A ((overCoordinateAlgebra A).obj (op (Over.mk (Spec.map f)))) M ≃+
      (ModuleCat.extendScalars f.hom).obj M :=
  (TensorProduct.congr (specCoordinateLinearEquiv A C f) (LinearEquiv.refl A M)).toAddEquiv

private lemma tensorPullbackSections_specMap (C : CommRingCat.{u}) (f : A ⟶ C)
    (M : ModuleCat A) (t : TensorProduct A
      ((overCoordinateAlgebra A).obj (op (Over.mk (Spec.map f)))) M) :
    (((AlgebraicGeometry.pullbackTildeIso A C f).hom.app M).app ⊤)
      (tensorPullbackSections A M (Over.mk (Spec.map f)) t) =
    tilde.toOpen ((ModuleCat.extendScalars f.hom).obj M) ⊤
      (tensorSpecCoordinateEquiv A C f M t) := by
  let q := ((AlgebraicGeometry.pullbackTildeIso A C f).hom.app M).app ⊤
  let η := tilde.toOpen ((ModuleCat.extendScalars f.hom).obj M) ⊤
  refine DFunLike.congr_fun (tensorAddHom_ext
    (f := q.hom.comp (tensorPullbackSections A M (Over.mk (Spec.map f))))
    (g := η.hom.toAddMonoidHom.comp (tensorSpecCoordinateEquiv A C f M).toAddMonoidHom)
    fun b m => ?_) t
  change q (tensorPullbackSections A M (Over.mk (Spec.map f)) (b ⊗ₜ[A] m)) =
    η (tensorSpecCoordinateEquiv A C f M (b ⊗ₜ[A] m))
  rw [tensorPullbackSections_tmul]
  have hsmul := Scheme.Modules.Hom.app_smul
    ((AlgebraicGeometry.pullbackTildeIso A C f).hom.app M)
    (b : Γ(Spec C, ⊤)) (pullbackSectionUnit A M (Over.mk (Spec.map f)) m)
  refine Eq.trans hsmul ?_
  have h :
      (((AlgebraicGeometry.pullbackTildeIso A C f).hom.app M).app ⊤)
        (pullbackSectionUnit A M (Over.mk (Spec.map f)) m) =
      tilde.toOpen ((ModuleCat.extendScalars f.hom).obj M) ⊤
        ((1 : C) ⊗ₜ[A, f.hom] m) :=
    AlgebraicGeometry.pullbackTildeIso_hom_app_unit_toOpen A C f M m
  rw [h]
  change Γ(Spec C, ⊤) at b
  let N := (ModuleCat.extendScalars f.hom).obj M
  let η : N →ₗ[C] Γ(tilde N, ⊤) := (tilde.toOpen N ⊤).hom
  let C' : Under A := Under.mk f
  change b • η ((1 : C') ⊗ₜ[A] m) =
    η (((Scheme.ΓSpecIso C).hom b : C') ⊗ₜ[A] m)
  let t0 : N := (1 : C') ⊗ₜ[A] m
  calc
    b • η t0 = (Scheme.ΓSpecIso C).hom b • η t0 := by
      rw [Scheme.Modules.smul_Spec_def]
      simp only [Iso.hom_inv_id_apply]
      change b • η t0 = ((Spec C).presheaf.map (𝟙 (op ⊤))) b • η t0
      rw [CategoryTheory.Functor.map_id]
      rfl
    _ = η ((Scheme.ΓSpecIso C).hom b • t0) := (η.map_smul _ _).symm
    _ = η (((Scheme.ΓSpecIso C).hom b : C') ⊗ₜ[A] m) := congrArg η
      (TensorProduct.tmul_eq_smul_one_tmul (R := A) (S := C')
        ((Scheme.ΓSpecIso C).hom b) m).symm

private lemma bijective_tensorPullbackSections_specMap (C : CommRingCat.{u})
    (f : A ⟶ C) (M : ModuleCat A) :
    Function.Bijective (tensorPullbackSections A M (Over.mk (Spec.map f))) := by
  let q := ((AlgebraicGeometry.pullbackTildeIso A C f).hom.app M).app ⊤
  have hq : Function.Bijective q := ConcreteCategory.bijective_of_isIso q
  have hc : Function.Bijective (fun t => q
      (tensorPullbackSections A M (Over.mk (Spec.map f)) t)) := by
    have he : (fun t => q (tensorPullbackSections A M (Over.mk (Spec.map f)) t)) =
        fun t => tilde.toOpen ((ModuleCat.extendScalars f.hom).obj M) ⊤
          (tensorSpecCoordinateEquiv A C f M t) :=
      funext (tensorPullbackSections_specMap A C f M)
    rw [he]
    exact (ConcreteCategory.bijective_of_isIso
      (tilde.toOpen ((ModuleCat.extendScalars f.hom).obj M) ⊤)).comp
        (tensorSpecCoordinateEquiv A C f M).bijective
  exact (hq.of_comp_iff' _).1 hc

private def tensorPullbackSectionsNat (M : ModuleCat A) :
    overCoordinateAlgebra A ⋙ baseChangeUnder A M ⟶
      quasiCoherentPresheafFunctor (Spec A) (tilde M) where
  app X := AddCommGrpCat.ofHom (tensorPullbackSections A M X.unop)
  naturality X Y g := by
    apply AddCommGrpCat.hom_ext
    apply tensorAddHom_ext
    intro b m
    have hnat := pullbackSectionUnit_naturality A M g.unop m
    have hsm := pullbackSectionsMap_smul (tilde M) g.unop
      (b : Γ(X.unop.left, ⊤)) (pullbackSectionUnit A M X.unop m)
    exact (hsm.trans (congrArg
      (fun z => g.unop.left.appTop (b : Γ(X.unop.left, ⊤)) • z) hnat)).symm

private lemma isIso_tensorPullbackSectionsNat_app (M : ModuleCat A)
    (X : Over (Spec A)) [IsAffine X.left] :
    IsIso ((tensorPullbackSectionsNat A M).app (op X)) := by
  let f : A ⟶ Γ(X.left, ⊤) := (Scheme.ΓSpecIso A).inv ≫ X.hom.appTop
  let e : X ≅ Over.mk (Spec.map f) := Over.isoMk X.left.isoSpec (by
    dsimp [f]
    rw [Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality,
      Category.assoc, ← Scheme.isoSpec_Spec_inv]
    simp)
  have : IsIso ((tensorPullbackSectionsNat A M).app (op (Over.mk (Spec.map f)))) :=
    (ConcreteCategory.isIso_iff_bijective _).2
      (bijective_tensorPullbackSections_specMap A _ f M)
  refine (isIso_comp_left_iff
    ((overCoordinateAlgebra A ⋙ baseChangeUnder A M).map e.hom.op) _).1 ?_
  rw [(tensorPullbackSectionsNat A M).naturality e.hom.op]
  infer_instance

/-- The rule `U ↦ M ⊗_A Γ(U, 𝒪_U)` is the associated module of `M̃` on this site: on an affine
object the canonical map `M ⊗_A Γ(U, 𝒪_U) ⟶ Γ(U, U.hom⁺ M̃)` is an isomorphism. -/
@[no_expose] public def baseChangePresheafIso (M : ModuleCat.{u} A) :
    baseChangePresheaf B A hS M ≅
      Stacks.Sites.associatedPresheaf (Spec A) (tilde M) (toOver B A hS) :=
  have _hall : ∀ X : (BigAffineFppf B (Spec A) hS)ᵒᵖ,
      IsIso ((Functor.whiskerLeft (toOver B A hS).op
        (tensorPullbackSectionsNat A M)).app X) := fun X =>
    have : IsAffine ((toOver B A hS).obj X.unop).left := X.unop.property
    isIso_tensorPullbackSectionsNat_app A M ((toOver B A hS).obj X.unop)
  have hiso : IsIso (Functor.whiskerLeft (toOver B A hS).op
      (tensorPullbackSectionsNat A M)) := NatIso.isIso_of_isIso_app _
  @asIso _ _ _ _ (Functor.whiskerLeft (toOver B A hS).op
    (tensorPullbackSectionsNat A M)) hiso

/-- **Stacks 0H0U.** Each term of the rule `U ↦ M ⊗_A Γ(U, 𝒪_U)` is a sheaf: a complex of
`A`-modules gives a complex of modules, not merely a complex of presheaves of modules. -/
@[stacks 0H0U "the rule is a complex of modules, not only of presheaves of modules"]
public theorem baseChangePresheaf_isSheaf (M : ModuleCat.{u} A) :
    Presheaf.IsSheaf (affineTopology B A hS) (baseChangePresheaf B A hS M) :=
  (Presheaf.isSheaf_of_iso_iff (baseChangePresheafIso B A hS M)).mpr
    (Stacks.Sites.isSheaf_associatedPresheaf_of_isContinuous (Spec A) (tilde M)
      (toOver B A hS) (affineTopology B A hS)
      (quasiCoherentPresheaf_isSheaf_fpqc' (Spec A) (tilde M)))

/-! ### The complex of modules attached to a complex of `A`-modules -/

/-- The structure sheaf of `(Aff/Spec A)_fppf`, the sheaf of rings of global functions. -/
public abbrev structureSheaf : Sheaf (affineTopology B A hS) RingCat.{u} :=
  Stacks.Sites.siteStructureSheaf (Spec A) (toOver B A hS) (affineTopology B A hS)
    (structurePresheaf_isSheaf B A hS)

/-- Base change as a functor from `A`-modules to sheaves of `𝒪`-modules on
`(Aff/Spec A)_fppf`. -/
public def baseChangeSheafFunctor :
    ModuleCat.{u} A ⥤ SheafOfModules.{u} (structureSheaf B A hS) where
  obj M := { val := baseChangeModule B A hS M
             isSheaf := baseChangePresheaf_isSheaf B A hS M }
  map f := { val := (baseChangeModuleFunctor B A hS).map f }
  map_id M := SheafOfModules.Hom.ext ((baseChangeModuleFunctor B A hS).map_id M)
  map_comp f g := SheafOfModules.Hom.ext ((baseChangeModuleFunctor B A hS).map_comp f g)

/-- Base change into sheaves of `𝒪`-modules is additive, so it extends termwise to
complexes. -/
public instance baseChangeSheafFunctor_additive :
    (baseChangeSheafFunctor B A hS).Additive where
  map_add {_M _N} f g :=
    SheafOfModules.Hom.ext
      (Functor.map_add (baseChangeModuleFunctor B A hS) (f := f) (g := g))

/-- **Stacks 0H0U.** The complex `F^•` of sheaves of `𝒪`-modules attached to a complex `M^•`
of `A`-modules: in degree `n` it is the rule `U ↦ M^n ⊗_A Γ(U, 𝒪_U)`, with the base changes of
the differentials of `M^•`. -/
@[stacks 0H0U "the displayed rule on a complex is a complex of modules"]
public abbrev baseChangeComplex : CochainComplex (ModuleCat.{u} A) ℤ ⥤
    CochainComplex (SheafOfModules.{u} (structureSheaf B A hS)) ℤ :=
  (baseChangeSheafFunctor B A hS).mapHomologicalComplex (ComplexShape.up ℤ)

end AlgebraicGeometry.BigAffineFppf

end
