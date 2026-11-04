module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.CartesianTerminalDense
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleQcqsPushforward
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FinitePresentationAffineSections
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.InternalHom
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentLocallyQuasicoherent
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EssentiallySmallInternalHom
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Sections over affine objects of the internal Hom out of a module of finite presentation

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids, `F` a module of finite
presentation and `G` a module on the fppf site of `𝒳` which is *cartesian along flat morphisms of
affines* (for every arrow `z ⟶ x` between objects lying over affine schemes, lying over a flat
morphism, `Γ(z, 𝒪) ⊗_{Γ(x, 𝒪)} G(x) ⟶ G(z)` is an isomorphism).  This file proves that the
internal Hom `𝓗om_{𝒪}(F, G)` of Stacks 03EM is again cartesian along flat morphisms of affines
(`AlgebraicGeometry.FibredSite.isIso_restrictionBaseChange_internalHomSheaf`, and
`AlgebraicGeometry.FibredSite.isIso_restrictionBaseChange_internalHomSheafSmall` for the internal
Hom of `Mod(𝒪_𝒳)` at module universe `u`).  This is the input (c') of Stacks 0771 (7).

The proof has two steps.

* *Sections over an affine object.*  For `F` quasi-coherent and `x` over an affine scheme,
  evaluation at the final object of the slice `𝒳/x` identifies `𝓗om(F, G)(x)` with
  `Hom_{Γ(x)}(F(x), G(x))`
  (`AlgebraicGeometry.FibredSite.bijective_evalLinear_of_isQuasicoherentOnSite`): the objects of
  `𝒳/x` over affine schemes are cover-dense, and on them `F` is cartesian over every map to the
  final object (`Stacks.PresheafOfModules.bijective_app_of_isTerminal_of_isCoverDense`).
* *Flat base change.*  Under these identifications and `F(z) = Γ(z) ⊗ F(x)`,
  `G(z) = Γ(z) ⊗ G(x)`, the restriction map of `𝓗om(F, G)` along `z ⟶ x` is
  `θ ↦ Γ(z) ⊗ θ`, a base change because `F(x)` is of finite presentation
  (`AlgebraicGeometry.FibredSite.finitePresentation_obj_of_isFinitePresentationOnSite`) and
  `Γ(z)` is flat over `Γ(x)` (`Module.FinitePresentation.isBaseChange_map`); this is
  `Stacks.PresheafOfModules.InternalHomSections.isIso_restrictionBaseChange_internalHom`.

Finite presentation is needed: for `F = G = 𝒪[p]`, the `p`-torsion of the structure sheaf on
`(Sch/ℤ)_{fppf}`, `F(Spec ℤ) = 0` while `id ∈ Hom(F, F)`, so the sections of `𝓗om(F, G)` over an
affine object are not `Hom(F(x), G(x))` in general.

## References

* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
* [Stacks Project, Tag 0764](https://stacks.math.columbia.edu/tag/0764)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe v u w₁ w₂

namespace Stacks.PresheafOfModules.InternalHomSections

/-- The scalar action on the sections of the internal Hom over `U`, read at the final object
`Over.mk (𝟙 U)` of the slice: it is the action of the scalar on the values. -/
theorem smulHom_app_overMk_id {C : Type*} [Category C] (O : Cᵒᵖ ⥤ CommRingCat.{u})
    (F G : PresheafOfModules.{u} (Oforget O)) (U : C) (f : (Oforget O).obj (op U))
    (α : (restrFun O U).obj F ⟶ (restrFun O U).obj G)
    (m : ((restrFun O U).obj F).obj (op (Over.mk (𝟙 U)))) :
    (smulHom O F G U f α).app (op (Over.mk (𝟙 U))) m =
      (show (ORestr O U).obj (op (Over.mk (𝟙 U))) from f) • α.app (op (Over.mk (𝟙 U))) m := by
  have hf : fRestr O U f (op (Over.mk (𝟙 U))) = f := by
    show ((Oforget O).map (𝟙 (op U))).hom f = f
    rw [CategoryTheory.Functor.map_id]
    rfl
  show fRestr O U f (op (Over.mk (𝟙 U))) • α.app (op (Over.mk (𝟙 U))) m = _
  rw [hf]

variable {D : Type w₁} [Category.{w₂} D] (O : Dᵒᵖ ⥤ CommRingCat.{u})
  (F G : PresheafOfModules.{u} (Oforget O))

/-- Evaluation at the final object `Over.mk (𝟙 x)` of a section over `x` of the internal Hom, as
an `O(x)`-linear map `F(x) ⟶ G(x)`. -/
noncomputable def evalLinear (x : D) :
    letI : Module (O.obj (op x)) (F.obj (op x)) :=
      inferInstanceAs (Module ((Oforget O).obj (op x)) _)
    letI : Module (O.obj (op x)) (G.obj (op x)) :=
      inferInstanceAs (Module ((Oforget O).obj (op x)) _)
    letI : Module (O.obj (op x)) ((internalHom O F G).obj (op x)) :=
      inferInstanceAs (Module ((Oforget O).obj (op x)) _)
    (internalHom O F G).obj (op x) →ₗ[O.obj (op x)]
      (F.obj (op x) →ₗ[O.obj (op x)] G.obj (op x)) :=
  letI : Module (O.obj (op x)) (F.obj (op x)) := inferInstanceAs (Module ((Oforget O).obj (op x)) _)
  letI : Module (O.obj (op x)) (G.obj (op x)) := inferInstanceAs (Module ((Oforget O).obj (op x)) _)
  letI : Module (O.obj (op x)) ((internalHom O F G).obj (op x)) :=
    inferInstanceAs (Module ((Oforget O).obj (op x)) _)
  { toFun := fun α =>
      { toFun := fun m => α.app (op (Over.mk (𝟙 x))) m
        map_add' := fun a b => map_add (α.app (op (Over.mk (𝟙 x)))).hom a b
        map_smul' := fun c m => (α.app (op (Over.mk (𝟙 x)))).hom.map_smul c m }
    map_add' := fun _ _ => rfl
    map_smul' := fun c α => LinearMap.ext (smulHom_app_overMk_id O F G x c α) }

omit [Category D] in
/-- **Flat base change of `Hom` out of a finitely presented module, transported.**  If `P` and
`Q` are identified with `Hom_A(M, N)` and `Hom_B(M', N')`, where `M' = B ⊗_A M` and
`N' = B ⊗_A N`, compatibly with `g` and `θ ↦ B ⊗ θ`, then `g` is a base change. -/
theorem isBaseChange_of_arrowCongr {A B M N M' N' P Q : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] [AddCommGroup M']
    [Module B M'] [AddCommGroup N'] [Module B N']
    [AddCommGroup P] [Module A P] [AddCommGroup Q] [Module B Q] [Module A Q]
    [IsScalarTower A B Q]
    (eF : TensorProduct A B M ≃ₗ[B] M') (eG : TensorProduct A B N ≃ₗ[B] N')
    (Ex : P ≃ₗ[A] (M →ₗ[A] N)) (Ez : Q ≃ₗ[B] (M' →ₗ[B] N')) (g : P →ₗ[A] Q)
    (key0 : ∀ (θ : M →ₗ[A] N) (c : B) (n : M), Ez (g (Ex.symm θ)) (eF (c ⊗ₜ n)) = eG (c ⊗ₜ θ n))
    (hflat : Module.Flat A B) (hfp : Module.FinitePresentation A M) :
    IsBaseChange B g := by
  have key : ∀ θ : M →ₗ[A] N,
      Ez (g (Ex.symm θ)) = LinearEquiv.arrowCongr eF eG (θ.baseChange B) := by
    intro θ
    refine LinearMap.ext fun m => ?_
    obtain ⟨w, rfl⟩ := eF.surjective m
    rw [LinearEquiv.arrowCongr_apply, eF.symm_apply_apply]
    induction w using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul c n =>
      rw [LinearMap.baseChange_tmul]
      exact key0 θ c n
  refine (IsBaseChange.iff_of_equiv_comm Ex.symm
    ((LinearEquiv.arrowCongr eF eG).trans Ez.symm) ?_).1
    (Module.FinitePresentation.isBaseChange_map A M N B)
  exact LinearMap.ext fun θ => Ez.injective ((key θ).trans (Ez.apply_symm_apply _).symm)

/-- The restriction of a section of the internal Hom along `f : z ⟶ x`, read at the final object
of the slice at `z`, is the section read at `Over.mk (𝟙 z ≫ f)`. -/
theorem internalHom_map_app {z x : D} (f : z ⟶ x)
    (α : (internalHom O F G).obj (op x)) (m : F.obj (op z)) :
    ((internalHom O F G).map f.op α).app (op (Over.mk (𝟙 z))) m =
      α.app (op (Over.mk (𝟙 z ≫ f))) m :=
  rfl

/-- Restricting a section of the internal Hom along `φ : z ⟶ x` and evaluating at the final
object over `z` on a restricted section is restricting the evaluation over `x`. -/
theorem evalLinear_map {z x : D} (φ : z ⟶ x) (α : (internalHom O F G).obj (op x))
    (n : F.obj (op x)) :
    ((internalHom O F G).map φ.op α).app (op (Over.mk (𝟙 z))) (F.map φ.op n) =
      G.map φ.op (α.app (op (Over.mk (𝟙 x))) n) :=
  (internalHom_map_app O F G φ α (F.map φ.op n)).trans
    (_root_.PresheafOfModules.naturality_apply α
      (Over.homMk φ (by simp) : Over.mk (𝟙 z ≫ φ) ⟶ Over.mk (𝟙 x)).op n)

/-- **The internal Hom is cartesian along `φ : z ⟶ x` when evaluation at the final objects of the
slices is bijective, `F` and `G` are cartesian along `φ`, `F(x)` is of finite presentation and
`O(z)` is flat over `O(x)`.**  Under the evaluations and the base-change isomorphisms of `F` and
`G`, the restriction map of the internal Hom is `θ ↦ O(z) ⊗ θ`, a base change for finitely
presented source and flat base change (`Module.FinitePresentation.isBaseChange_map`). -/
@[sga "3 III 0.6" "special case"]
theorem isIso_restrictionBaseChange_internalHom {z x : D} (φ : z ⟶ x)
    (hbx : Function.Bijective (evalLinear O F G x))
    (hbz : Function.Bijective (evalLinear O F G z))
    [IsIso (restrictionBaseChange (R := O) F φ.op)] [IsIso (restrictionBaseChange (R := O) G φ.op)]
    (hfp : Module.FinitePresentation ((Oforget O).obj (op x)) (F.obj (op x)))
    (hflat : (O.map φ.op).hom.Flat) :
    IsIso (restrictionBaseChange.{w₁, w₂, u, max w₁ w₂} (R := O) (internalHom O F G) φ.op) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  let H := internalHom O F G
  let A := O.obj (op x)
  let B := O.obj (op z)
  let : Module A (F.obj (op x)) := inferInstanceAs (Module ((Oforget O).obj (op x)) _)
  let : Module A (G.obj (op x)) := inferInstanceAs (Module ((Oforget O).obj (op x)) _)
  let : Module B (F.obj (op z)) := inferInstanceAs (Module ((Oforget O).obj (op z)) _)
  let : Module B (G.obj (op z)) := inferInstanceAs (Module ((Oforget O).obj (op z)) _)
  let : Module A (H.obj (op x)) := inferInstanceAs (Module ((Oforget O).obj (op x)) _)
  let : Module B (H.obj (op z)) := inferInstanceAs (Module ((Oforget O).obj (op z)) _)
  let : Algebra A B := (O.map φ.op).hom.toAlgebra
  let : Module A (H.obj (op z)) := Module.compHom _ (algebraMap A B)
  have : IsScalarTower A B (H.obj (op z)) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let eF : TensorProduct A B (F.obj (op x)) ≃ₗ[B] F.obj (op z) :=
    (asIso (restrictionBaseChange (R := O) F φ.op)).toLinearEquiv
  let eG : TensorProduct A B (G.obj (op x)) ≃ₗ[B] G.obj (op z) :=
    (asIso (restrictionBaseChange (R := O) G φ.op)).toLinearEquiv
  let rF : F.obj (op x) → F.obj (op z) := fun n => F.map φ.op n
  let rG : G.obj (op x) → G.obj (op z) := fun n => G.map φ.op n
  have heF : ∀ (c : B) (n : F.obj (op x)), eF (c ⊗ₜ n) = c • rF n :=
    restrictionBaseChange_tmul (R := O) F φ.op
  have heG : ∀ (c : B) (n : G.obj (op x)), eG (c ⊗ₜ n) = c • rG n :=
    restrictionBaseChange_tmul (R := O) G φ.op
  let Ex := LinearEquiv.ofBijective (evalLinear O F G x) hbx
  let Ez := LinearEquiv.ofBijective (evalLinear O F G z) hbz
  let g : H.obj (op x) →ₗ[A] H.obj (op z) :=
    { toFun := fun h => H.map φ.op h
      map_add' := fun a b => map_add (H.map φ.op).hom a b
      map_smul' := fun c a => H.map_smul φ.op c a }
  have key0 : ∀ (θ : F.obj (op x) →ₗ[A] G.obj (op x)) (c : B) (n : F.obj (op x)),
      Ez (g (Ex.symm θ)) (eF (c ⊗ₜ n)) = eG (c ⊗ₜ θ n) := fun θ c n => by
    rw [heF, map_smul, heG]
    exact congrArg (c • ·) ((evalLinear_map O F G φ (Ex.symm θ) n).trans
      (congrArg rG (LinearMap.congr_fun (Ex.apply_symm_apply θ) n)))
  exact bijective_restrictionBaseChange_of_isBaseChange.{w₂, w₁, u, max w₁ w₂} (R := O) H φ.op g
    (fun _ => rfl)
    (isBaseChange_of_arrowCongr eF eG Ex Ez g key0 hflat hfp)

end Stacks.PresheafOfModules.InternalHomSections

namespace Stacks.SheafOfModules

/-- **Shrinking the sections of a presheaf of modules preserves being cartesian over a
morphism.**  The shrunken sections are identified with the original ones by linear equivalences
compatible with the restriction maps (`Stacks.shrinkPresheaf_map_apply`). -/
theorem isIso_restrictionBaseChange_presheafShrink {C : Type w₁} [Category.{w₂} C]
    {R : Cᵒᵖ ⥤ CommRingCat.{u}}
    (M : PresheafOfModules.{max u v} (R ⋙ forget₂ CommRingCat RingCat))
    [∀ X, Small.{u} (M.obj X)] {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (h : IsIso (Stacks.PresheafOfModules.restrictionBaseChange.{w₁, w₂, u, v} M f)) :
    IsIso (Stacks.PresheafOfModules.restrictionBaseChange.{w₁, w₂, u, u}
      (presheafShrink.{u, v} (R ⋙ forget₂ CommRingCat RingCat) M) f) := by
  have hb : Function.Bijective (Stacks.PresheafOfModules.restrictionBaseChange M f) :=
    ConcreteCategory.bijective_of_isIso _
  let MS := presheafShrink.{u, v} (R ⋙ forget₂ CommRingCat RingCat) M
  let _ : Algebra (R.obj X) (R.obj Y) := (R.map f).hom.toAlgebra
  let : Module (R.obj Y) (M.obj Y) :=
    inferInstanceAs (Module ((R ⋙ forget₂ CommRingCat RingCat).obj Y) _)
  let : Module (R.obj X) (M.obj X) :=
    inferInstanceAs (Module ((R ⋙ forget₂ CommRingCat RingCat).obj X) _)
  let dY : Shrink.{u} (M.obj Y) ≃ₗ[R.obj Y] M.obj Y := Shrink.linearEquiv (R.obj Y) (M.obj Y)
  let dX : Shrink.{u} (M.obj X) ≃ₗ[R.obj X] M.obj X := Shrink.linearEquiv (R.obj X) (M.obj X)
  let e : TensorProduct (R.obj X) (R.obj Y) (Shrink.{u} (M.obj X)) ≃ₗ[R.obj Y]
      TensorProduct (R.obj X) (R.obj Y) (M.obj X) :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl (R.obj Y) (R.obj Y)) dX
  let L₁ : TensorProduct (R.obj X) (R.obj Y) (Shrink.{u} (M.obj X)) →ₗ[R.obj Y] M.obj Y :=
    dY.toLinearMap ∘ₗ (Stacks.PresheafOfModules.restrictionBaseChange.{w₁, w₂, u, u} MS f).hom
  let L₂ : TensorProduct (R.obj X) (R.obj Y) (Shrink.{u} (M.obj X)) →ₗ[R.obj Y] M.obj Y :=
    (Stacks.PresheafOfModules.restrictionBaseChange.{w₁, w₂, u, v} M f).hom ∘ₗ e.toLinearMap
  have key : L₁ = L₂ := by
    refine LinearMap.ext fun w => ?_
    induction w using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | add a c ha hc => rw [map_add, map_add, ha, hc]
    | tmul b x =>
      refine Eq.trans ?_
        (Stacks.PresheafOfModules.restrictionBaseChange_tmul.{w₁, w₂, u, v} M f b (dX x)).symm
      refine (congrArg dY (Stacks.PresheafOfModules.restrictionBaseChange_tmul.{w₁, w₂, u, u}
        MS f b x)).trans ?_
      refine (map_smul dY b _).trans ?_
      exact congrArg (fun y => b • y) (shrinkPresheaf_map_apply M.presheaf f x)
  have hfun : ((dY.symm : _ → _) ∘ (L₁ : _ → _)) =
      ((Stacks.PresheafOfModules.restrictionBaseChange.{w₁, w₂, u, u} MS f) : _ → _) :=
    funext fun _ => dY.symm_apply_apply _
  rw [ConcreteCategory.isIso_iff_bijective, ← hfun, key]
  exact dY.symm.bijective.comp (hb.comp e.bijective)

end Stacks.SheafOfModules

namespace AlgebraicGeometry.FibredSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{u} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- The objects of the slice `𝒳/x` lying over an affine scheme. -/
abbrev sliceIsAffine (x : 𝒳) : ObjectProperty (Over x) :=
  fun W => IsAffineOver B S hS (p.obj W.left)

include hp in
/-- **The objects of a slice of the associated fppf site lying over affine schemes are
cover-dense.** -/
theorem isCoverDense_sliceIsAffine_ι (x : 𝒳) :
    (sliceIsAffine B S hS p x).ι.IsCoverDense
      ((BigFppfOver.associatedTopology B S hS p .fppf).over x) where
  is_cover W := by
    obtain ⟨I, Y, a, haff, hcov⟩ := exists_affine_ofArrows_over B S hS p hp x W
    refine GrothendieckTopology.superset_covering _ (fun V g hg => ?_) hcov
    obtain ⟨j, h, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hg
    exact (Sieve.coverByImage _ W).downward_closed
      (Presieve.in_coverByImage (sliceIsAffine B S hS p x).ι
        (Y := (⟨Y j, haff j⟩ : (sliceIsAffine B S hS p x).FullSubcategory)) (a j)) h

/-- The restriction of a sheaf of modules on the fppf site of `𝒳` to the slice `𝒳/x` is a sheaf. -/
theorem isSheaf_over_forget_op_comp
    (G : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf)) (x : 𝒳) :
    Presheaf.IsSheaf ((BigFppfOver.associatedTopology B S hS p .fppf).over x)
      ((Over.forget x).op ⋙ G.val.presheaf) :=
  (((BigFppfOver.associatedTopology B S hS p .fppf).overPullback AddCommGrpCat.{u} x).obj
    ⟨G.val.presheaf, G.isSheaf⟩).property

include hp in
/-- **A morphism out of a quasi-coherent module on a slice over an affine object is determined by
its component at the final object, and every linear map is such a component.**  For `F`
quasi-coherent, `G` any module on the fppf site of `𝒳` and `x` an object lying over an affine
scheme, evaluation at `Over.mk (𝟙 x)` is a bijection from the morphisms `F|_{𝒳/x} ⟶ G|_{𝒳/x}`
(the sections over `x` of the internal Hom of Stacks 03EM) onto `Hom_{Γ(x)}(F(x), G(x))`.  The
objects of `𝒳/x` over affine schemes are cover-dense, and a quasi-coherent module is cartesian
between affine objects
(`Stacks.PresheafOfModules.bijective_app_of_isTerminal_of_isCoverDense`). -/
theorem bijective_app_restrFun_of_isQuasicoherentOnSite
    (F G : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf))
    (hF : F.IsQuasicoherentOnSite) {x : 𝒳}
    (hx : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x))) :
    Function.Bijective (fun α : (restrFun (structureSheaf B S hS p hp .fppf).obj x).obj F.val ⟶
        (restrFun (structureSheaf B S hS p hp .fppf).obj x).obj G.val =>
      α.app (op (Over.mk (𝟙 x)))) := by
  have := isCoverDense_sliceIsAffine_ι B S hS p hp x
  exact Stacks.PresheafOfModules.bijective_app_of_isTerminal_of_isCoverDense
    ((BigFppfOver.associatedTopology B S hS p .fppf).over x) (Over.forget x)
    (Rc := (structureSheaf B S hS p hp .fppf).obj) F.val G.val (sliceIsAffine B S hS p x)
    (isSheaf_over_forget_op_comp B S hS p hp G x)
    Over.mkIdTerminal hx (fun V hV => isIso_restrictionBaseChange_of_isQuasicoherentOnSite F hF
      (Over.mkIdTerminal.from V).left hV hx)

include hp in
/-- **The sections over `x` of the internal Hom out of a quasi-coherent module are the linear maps
of sections over `x`**, for `x` lying over an affine scheme: evaluation at the final object of the
slice, `Stacks.PresheafOfModules.InternalHomSections.evalLinear`, is bijective. -/
theorem bijective_evalLinear_of_isQuasicoherentOnSite
    (F G : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf))
    (hF : F.IsQuasicoherentOnSite) {x : 𝒳}
    (hx : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x))) :
    Function.Bijective (Stacks.PresheafOfModules.InternalHomSections.evalLinear
      (structureSheaf B S hS p hp .fppf).obj F.val G.val x) := by
  have h := bijective_app_restrFun_of_isQuasicoherentOnSite B S hS p hp F G hF hx
  refine ⟨fun α β hαβ => h.1 ?_, fun ψ => ?_⟩
  · ext m
    exact LinearMap.congr_fun hαβ m
  · obtain ⟨α, hα⟩ := h.2 (ModuleCat.ofHom
      (R := (structureSheaf B S hS p hp .fppf).obj.obj (op x))
      { toFun := fun m => ψ m
        map_add' := ψ.map_add
        map_smul' := fun c m => ψ.map_smul c m })
    exact ⟨α, LinearMap.ext fun m => congrArg (fun f => f.hom m) hα⟩

include hp in
/-- **The internal Hom out of a module of finite presentation into a module cartesian along flat
morphisms of affines is cartesian along flat morphisms of affines** (input (c') of Stacks 0771
(7)).  Let `F` be of finite presentation and `G` cartesian along flat morphisms of affines, on the
fppf site of `𝒳`, and let `φ : z ⟶ x` lie over a flat morphism of affine schemes.  The sections
over `x` of `𝓗om_{𝒪}(F, G)` are `Hom_{Γ(x)}(F(x), G(x))`
(`AlgebraicGeometry.FibredSite.bijective_app_restrFun_of_isQuasicoherentOnSite`, `F` being
quasi-coherent), likewise over `z`, and under these identifications the restriction map is
`θ ↦ Γ(z) ⊗ θ`, a base change because `F(x)` is of finite presentation and `Γ(z)` is flat over
`Γ(x)` (`Stacks.PresheafOfModules.InternalHomSections.isIso_restrictionBaseChange_internalHom`).

Finite presentation of `F` cannot be dropped: for `F = G = 𝒪[p]`, the `p`-torsion of the
structure sheaf on `(Sch/ℤ)_{fppf}`, `G` is cartesian along flat maps but `F(Spec ℤ) = 0` while
`id ∈ Hom(F, F)`, so the sections of `𝓗om(F, G)` over an affine are not `Hom(F(x), G(x))`. -/
theorem isIso_restrictionBaseChange_internalHomSheaf
    (F G : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf))
    [F.IsFinitePresentationOnSite]
    (hG : ∀ {z x : 𝒳} (φ : z ⟶ x), IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj z)) →
      IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x)) →
      Flat ((BigFppfOver.toScheme B S hS).map (p.map φ)) →
      IsIso (Stacks.PresheafOfModules.restrictionBaseChange
        (R := (structureSheaf B S hS p hp .fppf).obj) G.val φ.op))
    {z x : 𝒳} (φ : z ⟶ x) (hz : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj z)))
    (hx : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x)))
    (hφ : Flat ((BigFppfOver.toScheme B S hS).map (p.map φ))) :
    IsIso (Stacks.PresheafOfModules.restrictionBaseChange
      (R := (structureSheaf B S hS p hp .fppf).obj)
      (RingedSite.internalHomSheaf (ringedSite B S hS p hp .fppf) F G).val φ.op) := by
  have hFq : F.IsQuasicoherentOnSite := inferInstance
  have := isIso_restrictionBaseChange_of_isQuasicoherentOnSite F hFq φ hz hx
  have := hG φ hz hx hφ
  exact Stacks.PresheafOfModules.InternalHomSections.isIso_restrictionBaseChange_internalHom
    (structureSheaf B S hS p hp .fppf).obj F.val G.val φ
    (bijective_evalLinear_of_isQuasicoherentOnSite B S hS p hp F G hFq hx)
    (bijective_evalLinear_of_isQuasicoherentOnSite B S hS p hp F G hFq hz)
    (finitePresentation_obj_of_isFinitePresentationOnSite B S hS p hp F x hx)
    ((BigFppfOver.toScheme B S hS).map (p.map φ)).flat_appTop

include hp in
/-- **The internal Hom `SheafHom_{𝒪}(F, G)` of `Mod(𝒪_𝒳)` at module universe `u`
(`AlgebraicGeometry.RingedSite.internalHomSheafSmall`) out of a module of finite presentation
into a module cartesian along flat morphisms of affines is cartesian along flat morphisms of
affines.**  This is `AlgebraicGeometry.FibredSite.isIso_restrictionBaseChange_internalHomSheaf`
read on the shrunken sections. -/
theorem isIso_restrictionBaseChange_internalHomSheafSmall
    [EssentiallySmall.{u} (ringedSite B S hS p hp .fppf).C]
    (F G : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf))
    [F.IsFinitePresentationOnSite]
    (hG : ∀ {z x : 𝒳} (φ : z ⟶ x), IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj z)) →
      IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x)) →
      Flat ((BigFppfOver.toScheme B S hS).map (p.map φ)) →
      IsIso (Stacks.PresheafOfModules.restrictionBaseChange
        (R := (structureSheaf B S hS p hp .fppf).obj) G.val φ.op))
    {z x : 𝒳} (φ : z ⟶ x) (hz : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj z)))
    (hx : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x)))
    (hφ : Flat ((BigFppfOver.toScheme B S hS).map (p.map φ))) :
    IsIso (Stacks.PresheafOfModules.restrictionBaseChange
      (R := (structureSheaf B S hS p hp .fppf).obj)
      (RingedSite.internalHomSheafSmall.{u} (ringedSite B S hS p hp .fppf) F G).val φ.op) :=
  @Stacks.SheafOfModules.isIso_restrictionBaseChange_presheafShrink.{v, u, v, u} _ _
    (structureSheaf B S hS p hp .fppf).obj
    (RingedSite.internalHomSheaf (ringedSite B S hS p hp .fppf) F G).val
    (fun X => RingedSite.small_internalHomSheaf_obj (ringedSite B S hS p hp .fppf) F G X) _ _ φ.op
    (isIso_restrictionBaseChange_internalHomSheaf B S hS p hp F G hG φ hz hx hφ)

end AlgebraicGeometry.FibredSite
