module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.CoheratorMonoidal
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FppfTensorAffineSections
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentLocallyQuasicoherent
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorAssociatorSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafBraidingSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerConstraints
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FinitePresentationAffineSections
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactDiagonalGerbe
public import StacksFrontier.AlgebraicGeometry.Stacks.AffineMorphism
public import StacksFrontier.Algebra.Category.ModuleCat.Monoidal.RestrictScalarsBijective

/-!
# The pullback of quasi-coherent modules to a point over an affine scheme

Let `𝒳` be an algebraic stack over `S` and let `x` be an object of `𝒳` lying over a scheme
`X_x` together with an isomorphism `e : X_x ≅ Spec R`; this is a morphism `f : Spec R ⟶ 𝒳` in
the 2-Yoneda description of points.  The pullback `f^* : QCoh(𝒪_𝒳) ⥤ Mod_R` of Stacks 0GRK and
0GRP is the functor of sections at `x`, `M ↦ M(x)`, read as an `R`-module through
`R ≅ Γ(Spec R, 𝒪) ≅ Γ(X_x, 𝒪) = 𝒪_𝒳(x)`.

The functor `f^*` is a *tensor functor*: it is additive, and strong symmetric monoidal for
the symmetric monoidal structure on `QCoh(𝒪_𝒳)` of Stacks 0GQM (the tensor product sheaf of
Tag 01CA restricted to quasi-coherent modules) and that of `ModuleCat R`.  The tensorator
`M(x) ⊗_R N(x) ⟶ (M ⊗ N)(x)` is the sheafification unit at `x` of the objectwise tensor product,
which is bijective because `x` lies over an affine scheme and quasi-coherent modules are
cartesian between affine objects; the unit is `R ≅ 𝒪_𝒳(x)`.

A 2-arrow, i.e. an isomorphism `a : x ≅ y` of `𝒳` lying over the identity of `Spec R`, induces
an isomorphism of tensor functors `f_x^* ≅ f_y^*`: on `M` it is restriction `M(x) ⟶ M(y)` along
`a⁻¹`.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.pointPullback`: `f^* : QCoh(𝒪_𝒳) ⥤ ModuleCat R`,
  with instances `pointPullbackMonoidal`, `pointPullbackBraided` and `pointPullbackAdditive`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.pointPullbackTransportIso`: the isomorphism
  `f_x^* ≅ f_y^*` induced by a 2-arrow, monoidal by `isMonoidal_pointPullbackTransportIso`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.overSpecIso`: the identification `X_x ≅ Spec R` for a
  point with `p x = (Spec R → S)`, and `toScheme_map_comp_overSpecIso`, which makes a 2-arrow in
  that presentation an input of `pointPullbackTransportIso`.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.bijective_pointTensorMap`: sections over a point over
  an affine scheme commute with tensor products of quasi-coherent modules.
* `AlgebraicGeometry.Stack.AlgebraicStacks.finite_pointPullback_obj`: `f^*` carries a module of
  finite presentation to a finitely generated `R`-module.

## References

* [Stacks Project, Tag 0GRK](https://stacks.math.columbia.edu/tag/0GRK)
* [Stacks Project, Tag 0GRP](https://stacks.math.columbia.edu/tag/0GRP)
* [Stacks Project, Tag 0GQM](https://stacks.math.columbia.edu/tag/0GQM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite Functor.LaxMonoidal
open scoped TensorProduct

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

attribute [local instance] hasSheafCompose_forget_ringCat
  hasSheafCompose_forget_commRingCat Stacks.hasSheafCompose_forget₂_commRingCat
  FlatFppf.hasSheafify_addCommGrpCat FlatFppf.wEqualsLocallyBijective_addCommGrpCat
  FlatFppf.hasSheafify_fppf_addCommGrpCat FlatFppf.wEqualsLocallyBijective_fppf_addCommGrpCat
  FlatFppf.hasSheafify_associatedTopology_ab
  FlatFppf.wEqualsLocallyBijective_fppfTopology_addCommGrpCat
attribute [local instance] fppfModulesMonoidal fppfModulesBraided fppfModulesSymmetric
attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : AlgebraicStacks.{u, w} B S hS) (x : 𝒳.val.val.obj)

/-- The structure presheaf of commutative rings of the fppf site of `𝒳`. -/
abbrev fppfStructurePresheaf : (𝒳.val.val.obj)ᵒᵖ ⥤ CommRingCat.{u} :=
  (FibredSite.structureSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf).obj

/-- The structure presheaf of the fppf site of `𝒳` is a sheaf. -/
theorem fppfStructurePresheaf_isSheaf :
    Presheaf.IsSheaf (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf)
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf
        (fppfStructurePresheaf B S hS 𝒳)) :=
  FibredSite.structureRingPresheaf_isSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf

variable {R : Type u} [CommRing R]
  (e : (BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x) ≅ Spec (CommRingCat.of R))

/-- The ring isomorphism `R ≅ Γ(x, 𝒪)` induced by `x ↦ Spec R`. -/
def pointRingIso : CommRingCat.of R ≅ (fppfStructurePresheaf B S hS 𝒳).obj (op x) :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).symm ≪≫ Scheme.Γ.mapIso e.op

/-- The ring map `R → Γ(x, 𝒪)` induced by `x ↦ Spec R`. -/
def pointRingHom : R →+* (fppfStructurePresheaf B S hS 𝒳).obj (op x) :=
  (pointRingIso B S hS 𝒳 x e).hom.hom

/-- **The pullback `f^* : QCoh(𝒪_𝒳) ⥤ Mod_R` along a point `f : Spec R ⟶ 𝒳`**, given by an object
`x` of `𝒳` and an isomorphism `e` of the scheme under `x` with `Spec R`: the sections `M(x)`,
an `R`-module through `R ≅ 𝒪_𝒳(x)`. -/
def pointPullback : quasicoherentModules B S hS 𝒳 ⥤ ModuleCat.{u} R :=
  quasicoherentInclusion B S hS 𝒳 ⋙ SheafOfModules.forget _ ⋙
    PresheafOfModules.evaluation _ (op x) ⋙ ModuleCat.restrictScalars (pointRingHom B S hS 𝒳 x e)

/-- The underlying presheaf of modules of a quasi-coherent module, over the structure presheaf
spelled as the monoidal structure of presheaves of modules expects. -/
abbrev modulesPresheaf (M : quasicoherentModules B S hS 𝒳) :
    PresheafOfModules.{u} (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf
      (fppfStructurePresheaf B S hS 𝒳)) :=
  M.obj.val

/-- The sheafification unit at `x` of the objectwise tensor product, `M(x) ⊗ N(x) ⟶ (M ⊗ N)(x)`. -/
def pointTensorMap (M N : quasicoherentModules B S hS 𝒳) :
    (modulesPresheaf B S hS 𝒳 M ⊗ modulesPresheaf B S hS 𝒳 N).obj (op x) ⟶
      (M ⊗ N).obj.val.obj (op x) :=
  (Stacks.SheafOfModules.TensorSheafification.toSheafify (fppfStructurePresheaf B S hS 𝒳)
    (fppfStructurePresheaf_isSheaf B S hS 𝒳)
    (modulesPresheaf B S hS 𝒳 M ⊗ modulesPresheaf B S hS 𝒳 N)).app (op x)

/-- The tensor product of two morphisms on a pure tensor at `x`. -/
theorem tensorHom_pointTensorMap {M M' N N' : quasicoherentModules B S hS 𝒳} (f : M ⟶ M')
    (g : N ⟶ N') (m : (modulesPresheaf B S hS 𝒳 M).obj (op x))
    (n : (modulesPresheaf B S hS 𝒳 N).obj (op x)) :
    (f ⊗ₘ g).hom.val.app (op x) ((pointTensorMap B S hS 𝒳 x M N).hom (m ⊗ₜ n)) =
      (pointTensorMap B S hS 𝒳 x M' N').hom (f.hom.val.app (op x) m ⊗ₜ g.hom.val.app (op x) n) :=
  (congrArg (fun h => h.val.app (op x) ((pointTensorMap B S hS 𝒳 x M N).hom (m ⊗ₜ n)))
    (Stacks.SheafOfModules.tensorHom_eq_sheafify_map (fppfStructurePresheaf B S hS 𝒳)
      (fppfStructurePresheaf_isSheaf B S hS 𝒳) f.hom g.hom)).trans
    (Stacks.SheafOfModules.sheafify_map_toSheafify_app (fppfStructurePresheaf B S hS 𝒳)
      (fppfStructurePresheaf_isSheaf B S hS 𝒳) (f.hom.val ⊗ₘ g.hom.val) (op x) (m ⊗ₜ n))

/-- The associator of `QCoh(𝒪_𝒳)` on iterated pure tensors at `x`. -/
theorem associator_pointTensorMap (M N P : quasicoherentModules B S hS 𝒳)
    (m : (modulesPresheaf B S hS 𝒳 M).obj (op x)) (n : (modulesPresheaf B S hS 𝒳 N).obj (op x))
    (p : (modulesPresheaf B S hS 𝒳 P).obj (op x)) :
    (α_ M N P).hom.hom.val.app (op x) ((pointTensorMap B S hS 𝒳 x (M ⊗ N) P).hom
      ((pointTensorMap B S hS 𝒳 x M N).hom (m ⊗ₜ n) ⊗ₜ p)) =
      (pointTensorMap B S hS 𝒳 x M (N ⊗ P)).hom (m ⊗ₜ (pointTensorMap B S hS 𝒳 x N P).hom
        (n ⊗ₜ p)) :=
  Stacks.SheafOfModules.associator_hom_val_app_tmul (fppfStructurePresheaf B S hS 𝒳)
    (fppfStructurePresheaf_isSheaf B S hS 𝒳) M.obj N.obj P.obj (op x) m n p

/-- The left unitor of `QCoh(𝒪_𝒳)` on a pure tensor at `x`. -/
theorem leftUnitor_pointTensorMap (M : quasicoherentModules B S hS 𝒳)
    (r : (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf
      (fppfStructurePresheaf B S hS 𝒳)).obj (op x)) (m : (modulesPresheaf B S hS 𝒳 M).obj (op x)) :
    (λ_ M).hom.hom.val.app (op x) ((pointTensorMap B S hS 𝒳 x (𝟙_ _) M).hom (r ⊗ₜ m)) =
      r • m :=
  Stacks.SheafOfModules.leftUnitor_hom_val_app_tmul (fppfStructurePresheaf B S hS 𝒳)
    (fppfStructurePresheaf_isSheaf B S hS 𝒳) M.obj (op x) r m

/-- The right unitor of `QCoh(𝒪_𝒳)` on a pure tensor at `x`. -/
theorem rightUnitor_pointTensorMap (M : quasicoherentModules B S hS 𝒳)
    (r : (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf
      (fppfStructurePresheaf B S hS 𝒳)).obj (op x)) (m : (modulesPresheaf B S hS 𝒳 M).obj (op x)) :
    (ρ_ M).hom.hom.val.app (op x) ((pointTensorMap B S hS 𝒳 x M (𝟙_ _)).hom (m ⊗ₜ r)) =
      r • m :=
  Stacks.SheafOfModules.rightUnitor_hom_val_app_tmul (fppfStructurePresheaf B S hS 𝒳)
    (fppfStructurePresheaf_isSheaf B S hS 𝒳) M.obj (op x) m r

/-- The braiding of `QCoh(𝒪_𝒳)` on a pure tensor at `x`. -/
theorem braiding_pointTensorMap (M N : quasicoherentModules B S hS 𝒳)
    (m : (modulesPresheaf B S hS 𝒳 M).obj (op x)) (n : (modulesPresheaf B S hS 𝒳 N).obj (op x)) :
    (β_ M N).hom.hom.val.app (op x) ((pointTensorMap B S hS 𝒳 x M N).hom (m ⊗ₜ n)) =
      (pointTensorMap B S hS 𝒳 x N M).hom (n ⊗ₜ m) :=
  Stacks.SheafOfModules.braiding_tensorSectionsAt (fppfStructurePresheaf B S hS 𝒳)
    (fppfStructurePresheaf_isSheaf B S hS 𝒳) (op x) M.obj N.obj m n

/-- The tensorator of `pointPullback`. -/
def pointPullbackμ (M N : quasicoherentModules B S hS 𝒳) :
    (pointPullback B S hS 𝒳 x e).obj M ⊗ (pointPullback B S hS 𝒳 x e).obj N ⟶
      (pointPullback B S hS 𝒳 x e).obj (M ⊗ N) :=
  μ (ModuleCat.restrictScalars (pointRingHom B S hS 𝒳 x e))
      ((modulesPresheaf B S hS 𝒳 M).obj (op x))
      ((modulesPresheaf B S hS 𝒳 N).obj (op x)) ≫
    (ModuleCat.restrictScalars (pointRingHom B S hS 𝒳 x e)).map (pointTensorMap B S hS 𝒳 x M N)

/-- The tensorator of `pointPullback` on a pure tensor. -/
theorem pointPullbackμ_tmul (M N : quasicoherentModules B S hS 𝒳)
    (m : (pointPullback B S hS 𝒳 x e).obj M) (n : (pointPullback B S hS 𝒳 x e).obj N) :
    (pointPullbackμ B S hS 𝒳 x e M N).hom (m ⊗ₜ n) =
      ((pointTensorMap B S hS 𝒳 x M N).hom (m ⊗ₜ n) : (pointPullback B S hS 𝒳 x e).obj (M ⊗ N)) :=
  congrArg (pointTensorMap B S hS 𝒳 x M N).hom
    (ModuleCat.restrictScalars_μ_tmul (pointRingHom B S hS 𝒳 x e) _ _ m n)

/-- `pointPullback` on morphisms is the component at `x`. -/
theorem pointPullback_map_apply {M N : quasicoherentModules B S hS 𝒳} (f : M ⟶ N)
    (m : (pointPullback B S hS 𝒳 x e).obj M) :
    ((pointPullback B S hS 𝒳 x e).map f).hom m = f.hom.val.app (op x) m :=
  rfl

/-- `pointPullback` is lax monoidal, with tensorator `pointPullbackμ`. -/
instance pointPullbackLaxMonoidal : (pointPullback B S hS 𝒳 x e).LaxMonoidal where
  ε := ε (ModuleCat.restrictScalars (pointRingHom B S hS 𝒳 x e))
  μ := pointPullbackμ B S hS 𝒳 x e
  μ_natural_left {M M'} f N := by
    refine ModuleCat.MonoidalCategory.tensor_ext fun m n => ?_
    refine (pointPullbackμ_tmul B S hS 𝒳 x e M' N _ n).trans ?_
    refine (tensorHom_pointTensorMap B S hS 𝒳 x f (𝟙 N) m n).symm.trans ?_
    refine (congrArg (fun h => h.hom.val.app (op x) ((pointTensorMap B S hS 𝒳 x M N).hom
      (m ⊗ₜ n))) (tensorHom_id f N)).trans ?_
    exact congrArg (fun t => (f ▷ N).hom.val.app (op x) t)
      (pointPullbackμ_tmul B S hS 𝒳 x e M N m n).symm
  μ_natural_right {N N'} M g := by
    refine ModuleCat.MonoidalCategory.tensor_ext fun m n => ?_
    refine (pointPullbackμ_tmul B S hS 𝒳 x e M N' m _).trans ?_
    refine (tensorHom_pointTensorMap B S hS 𝒳 x (𝟙 M) g m n).symm.trans ?_
    refine (congrArg (fun h => h.hom.val.app (op x) ((pointTensorMap B S hS 𝒳 x M N).hom
      (m ⊗ₜ n))) (id_tensorHom M g)).trans ?_
    exact congrArg (fun t => (M ◁ g).hom.val.app (op x) t)
      (pointPullbackμ_tmul B S hS 𝒳 x e M N m n).symm
  associativity M N P := by
    refine ModuleCat.MonoidalCategory.tensor_ext₃' fun m n p => ?_
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
    rw [ModuleCat.MonoidalCategory.whiskerRight_apply,
      ModuleCat.MonoidalCategory.associator_hom_apply,
      ModuleCat.MonoidalCategory.whiskerLeft_apply,
      pointPullbackμ_tmul B S hS 𝒳 x e (M ⊗ N) P, pointPullbackμ_tmul B S hS 𝒳 x e M N,
      pointPullbackμ_tmul B S hS 𝒳 x e M (N ⊗ P), pointPullbackμ_tmul B S hS 𝒳 x e N P]
    exact associator_pointTensorMap B S hS 𝒳 x M N P m n p
  left_unitality M := by
    refine ModuleCat.MonoidalCategory.tensor_ext fun r m => ?_
    refine (ModuleCat.MonoidalCategory.leftUnitor_hom_apply r m).trans ?_
    refine Eq.trans ?_ (congrArg (fun t => (λ_ M).hom.hom.val.app (op x) t)
      (pointPullbackμ_tmul B S hS 𝒳 x e (𝟙_ _) M _ m)).symm
    refine Eq.trans ?_ (leftUnitor_pointTensorMap B S hS 𝒳 x M _ m).symm
    exact congrArg (fun s : (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf
      (fppfStructurePresheaf B S hS 𝒳)).obj (op x) =>
        s • (show (modulesPresheaf B S hS 𝒳 M).obj (op x) from m))
      (ModuleCat.restrictScalars_η (pointRingHom B S hS 𝒳 x e) r).symm
  right_unitality M := by
    refine ModuleCat.MonoidalCategory.tensor_ext fun m r => ?_
    refine (ModuleCat.MonoidalCategory.rightUnitor_hom_apply m r).trans ?_
    refine Eq.trans ?_ (congrArg (fun t => (ρ_ M).hom.hom.val.app (op x) t)
      (pointPullbackμ_tmul B S hS 𝒳 x e M (𝟙_ _) m _)).symm
    refine Eq.trans ?_ (rightUnitor_pointTensorMap B S hS 𝒳 x M _ m).symm
    exact congrArg (fun s : (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf
      (fppfStructurePresheaf B S hS 𝒳)).obj (op x) =>
        s • (show (modulesPresheaf B S hS 𝒳 M).obj (op x) from m))
      (ModuleCat.restrictScalars_η (pointRingHom B S hS 𝒳 x e) r).symm

/-- `R ⟶ 𝒪_𝒳(x)` is bijective. -/
theorem bijective_pointRingHom : Function.Bijective (pointRingHom B S hS 𝒳 x e) :=
  (ConcreteCategory.isIso_iff_bijective (pointRingIso B S hS 𝒳 x e).hom).1 inferInstance

include e in
/-- A point over `Spec R` lies over an affine scheme. -/
theorem isAffine_point : IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x)) :=
  IsAffine.of_isIso e.hom

include e in
/-- **Sections at a point over an affine scheme commute with tensor products** of
quasi-coherent modules: the sheafification unit at `x` is bijective. -/
theorem bijective_pointTensorMap (M N : quasicoherentModules B S hS 𝒳) :
    Function.Bijective (pointTensorMap B S hS 𝒳 x M N).hom :=
  FibredSite.bijective_sheafTensor_unit_app_of_isAffine B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids M.obj N.obj
    (fun φ hz hx _ => FibredSite.isIso_restrictionBaseChange_of_isQuasicoherentOnSite M.obj
      M.property φ hz hx)
    (fun φ hz hx _ => FibredSite.isIso_restrictionBaseChange_of_isQuasicoherentOnSite N.obj
      N.property φ hz hx)
    (isAffine_point B S hS 𝒳 x e)

/-- The unit of `pointPullback` is invertible. -/
instance isIso_ε_pointPullback : IsIso (ε (pointPullback B S hS 𝒳 x e)) := by
  refine (ConcreteCategory.isIso_iff_bijective _).2 ?_
  have h : ∀ r, (ε (pointPullback B S hS 𝒳 x e)).hom r = pointRingHom B S hS 𝒳 x e r :=
    ModuleCat.restrictScalars_η (pointRingHom B S hS 𝒳 x e)
  exact (funext h ▸ bijective_pointRingHom B S hS 𝒳 x e :)

/-- The tensorator of `pointPullback` is invertible. -/
instance isIso_μ_pointPullback (M N : quasicoherentModules B S hS 𝒳) :
    IsIso (μ (pointPullback B S hS 𝒳 x e) M N) :=
  (ConcreteCategory.isIso_iff_bijective _).2 <| (bijective_pointTensorMap B S hS 𝒳 x e M N).comp
    (ModuleCat.bijective_μ_restrictScalars _ (bijective_pointRingHom B S hS 𝒳 x e) _ _)

/-- `pointPullback` is a monoidal functor. -/
instance pointPullbackMonoidal : (pointPullback B S hS 𝒳 x e).Monoidal :=
  (Functor.CoreMonoidal.ofLaxMonoidal (pointPullback B S hS 𝒳 x e)).toMonoidal

/-- The tensorator of the monoidal functor `pointPullback` is `pointPullbackμ`. -/
theorem μ_pointPullback (M N : quasicoherentModules B S hS 𝒳) :
    μ (pointPullback B S hS 𝒳 x e) M N = pointPullbackμ B S hS 𝒳 x e M N :=
  rfl

/-- The tensorator of `pointPullback` is compatible with the braidings. -/
theorem pointPullback_braided (M N : quasicoherentModules B S hS 𝒳) :
    μ (pointPullback B S hS 𝒳 x e) M N ≫ (pointPullback B S hS 𝒳 x e).map (β_ M N).hom =
      (β_ ((pointPullback B S hS 𝒳 x e).obj M) ((pointPullback B S hS 𝒳 x e).obj N)).hom ≫
        μ (pointPullback B S hS 𝒳 x e) N M := by
  refine ModuleCat.MonoidalCategory.tensor_ext fun m n => ?_
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [ModuleCat.MonoidalCategory.braiding_hom_apply, pointPullback_map_apply]
  exact ((congrArg ((β_ M N).hom.hom.val.app (op x))
    (pointPullbackμ_tmul B S hS 𝒳 x e M N m n)).trans
    (braiding_pointTensorMap B S hS 𝒳 x M N m n)).trans
    (pointPullbackμ_tmul B S hS 𝒳 x e N M n m).symm

/-- `pointPullback` is a braided functor. -/
instance pointPullbackBraided : (pointPullback B S hS 𝒳 x e).Braided :=
  { pointPullbackMonoidal B S hS 𝒳 x e with
    braided := pointPullback_braided B S hS 𝒳 x e }

/-- `pointPullback` is additive. -/
instance pointPullbackAdditive : (pointPullback B S hS 𝒳 x e).Additive where
  map_add := rfl

section Transport

variable {x} {y : 𝒳.val.val.obj}
  (ey : (BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj y) ≅ Spec (CommRingCat.of R))
  (a : x ≅ y)
  (ha : (BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map a.hom) ≫ ey.hom = e.hom)

include ha in
/-- The inverse of a 2-arrow is compatible with the two identifications with `Spec R`. -/
theorem toScheme_map_inv_comp :
    (BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map a.inv) ≫ e.hom = ey.hom := by
  rw [← ha, ← Functor.map_comp_assoc, ← Functor.map_comp, a.inv_hom_id]
  simp

include ha in
/-- Restriction along `a⁻¹` carries `R ⟶ 𝒪_𝒳(x)` to `R ⟶ 𝒪_𝒳(y)`. -/
theorem fppfStructurePresheaf_map_pointRingHom (r : R) :
    (fppfStructurePresheaf B S hS 𝒳).map a.inv.op (pointRingHom B S hS 𝒳 x e r) =
      pointRingHom B S hS 𝒳 y ey r := by
  show (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map a.inv)).op)
      ((Scheme.Γ.map e.hom.op) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)) =
    (Scheme.Γ.map ey.hom.op) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)
  rw [← toScheme_map_inv_comp B S hS 𝒳 e ey a ha, op_comp, Functor.map_comp]
  rfl

include ha in
/-- `R ⟶ 𝒪_𝒳(y)` factors through `R ⟶ 𝒪_𝒳(x)` and restriction along `a⁻¹`. -/
theorem pointRingHom_eq_comp :
    pointRingHom B S hS 𝒳 y ey =
      ((Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf
        (fppfStructurePresheaf B S hS 𝒳)).map a.inv.op).hom.comp (pointRingHom B S hS 𝒳 x e) :=
  RingHom.ext fun r => (fppfStructurePresheaf_map_pointRingHom B S hS 𝒳 e ey a ha r).symm

/-- The map `M(x) ⟶ M(y)` induced by a 2-arrow, i.e. restriction along `a⁻¹ : y ⟶ x`. -/
def pointPullbackTransportApp (M : quasicoherentModules B S hS 𝒳) :
    (pointPullback B S hS 𝒳 x e).obj M ⟶ (pointPullback B S hS 𝒳 y ey).obj M :=
  (ModuleCat.restrictScalars (pointRingHom B S hS 𝒳 x e)).map
      ((modulesPresheaf B S hS 𝒳 M).map a.inv.op) ≫
    (ModuleCat.restrictScalarsComp'App (pointRingHom B S hS 𝒳 x e)
      ((Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf
        (fppfStructurePresheaf B S hS 𝒳)).map a.inv.op).hom (pointRingHom B S hS 𝒳 y ey)
      (pointRingHom_eq_comp B S hS 𝒳 e ey a ha) ((modulesPresheaf B S hS 𝒳 M).obj (op y))).inv

/-- The component of `pointPullbackTransport` is restriction along `a⁻¹`. -/
theorem pointPullbackTransportApp_apply (M : quasicoherentModules B S hS 𝒳)
    (m : (pointPullback B S hS 𝒳 x e).obj M) :
    (pointPullbackTransportApp B S hS 𝒳 e ey a ha M).hom m =
      (modulesPresheaf B S hS 𝒳 M).map a.inv.op m :=
  rfl

/-- The natural transformation `f_x^* ⟶ f_y^*` induced by a 2-arrow `a : x ≅ y` over `Spec R`. -/
def pointPullbackTransport : pointPullback B S hS 𝒳 x e ⟶ pointPullback B S hS 𝒳 y ey where
  app M := pointPullbackTransportApp B S hS 𝒳 e ey a ha M
  naturality M N f := by
    refine ModuleCat.hom_ext (LinearMap.ext fun m => ?_)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, pointPullbackTransportApp_apply,
      pointPullback_map_apply]
    exact (PresheafOfModules.naturality_apply f.hom.val a.inv.op m).symm

/-- The transport along a 2-arrow is a monoidal natural transformation. -/
instance isMonoidal_pointPullbackTransport :
    NatTrans.IsMonoidal (pointPullbackTransport B S hS 𝒳 e ey a ha) where
  unit := by
    refine ModuleCat.hom_ext (LinearMap.ext fun r => ?_)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
    refine (congrArg (pointPullbackTransportApp B S hS 𝒳 e ey a ha (𝟙_ _)).hom
      (ModuleCat.restrictScalars_η (pointRingHom B S hS 𝒳 x e) r)).trans ?_
    exact (fppfStructurePresheaf_map_pointRingHom B S hS 𝒳 e ey a ha r).trans
      (ModuleCat.restrictScalars_η (pointRingHom B S hS 𝒳 y ey) r).symm
  tensor M N := by
    refine ModuleCat.MonoidalCategory.tensor_ext fun m n => ?_
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, μ_pointPullback]
    rw [ModuleCat.MonoidalCategory.tensorHom_tmul, pointPullbackμ_tmul, pointPullbackμ_tmul]
    refine (PresheafOfModules.naturality_apply
      (Stacks.SheafOfModules.TensorSheafification.toSheafify
      (fppfStructurePresheaf B S hS 𝒳) (fppfStructurePresheaf_isSheaf B S hS 𝒳)
        (modulesPresheaf B S hS 𝒳 M ⊗ modulesPresheaf B S hS 𝒳 N)) a.inv.op (m ⊗ₜ n)).symm.trans ?_
    exact congrArg (pointTensorMap B S hS 𝒳 y M N).hom
      (PresheafOfModules.Monoidal.tensorObj_map_tmul _ _ _)

include ha in
/-- The inverse 2-arrow `a.symm` satisfies the compatibility of `pointPullbackTransport`. -/
theorem toScheme_map_symm_comp :
    (BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map a.symm.hom) ≫ e.hom = ey.hom :=
  toScheme_map_inv_comp B S hS 𝒳 e ey a ha

/-- **The natural isomorphism `f_x^* ≅ f_y^*` induced by a 2-arrow `a : x ≅ y` over `Spec R`**,
`M(x) ⟶ M(y)` being restriction along `a⁻¹`. -/
def pointPullbackTransportIso : pointPullback B S hS 𝒳 x e ≅ pointPullback B S hS 𝒳 y ey where
  hom := pointPullbackTransport B S hS 𝒳 e ey a ha
  inv := pointPullbackTransport B S hS 𝒳 ey e a.symm (toScheme_map_symm_comp B S hS 𝒳 e ey a ha)
  hom_inv_id := by
    ext M m
    exact ((modulesPresheaf B S hS 𝒳 M).map_comp_apply a.inv.op a.hom.op m).symm.trans
      (by rw [← op_comp, a.hom_inv_id, op_id, PresheafOfModules.map_id]; rfl)
  inv_hom_id := by
    ext M m
    exact ((modulesPresheaf B S hS 𝒳 M).map_comp_apply a.hom.op a.inv.op m).symm.trans
      (by rw [← op_comp, a.inv_hom_id, op_id, PresheafOfModules.map_id]; rfl)

/-- The component of `pointPullbackTransportIso` is restriction along `a⁻¹`. -/
theorem pointPullbackTransportIso_hom_app_apply (M : quasicoherentModules B S hS 𝒳)
    (m : (pointPullback B S hS 𝒳 x e).obj M) :
    ((pointPullbackTransportIso B S hS 𝒳 e ey a ha).hom.app M).hom m =
      M.obj.val.map a.inv.op m :=
  rfl

/-- The isomorphism induced by a 2-arrow is an isomorphism of tensor functors. -/
instance isMonoidal_pointPullbackTransportIso :
    NatTrans.IsMonoidal (pointPullbackTransportIso B S hS 𝒳 e ey a ha).hom :=
  isMonoidal_pointPullbackTransport B S hS 𝒳 e ey a ha

end Transport

include e in
/-- The sections of a module of finite presentation at a point over `Spec R` form a finitely
generated `R`-module. -/
theorem finite_pointPullback_obj (M : quasicoherentModules B S hS 𝒳)
    [M.obj.IsFinitePresentationOnSite] : Module.Finite R ((pointPullback B S hS 𝒳 x e).obj M) := by
  have hfp : Module.FinitePresentation ((fppfStructurePresheaf B S hS 𝒳).obj (op x))
      ((modulesPresheaf B S hS 𝒳 M).obj (op x)) :=
    FibredSite.finitePresentation_obj_of_isFinitePresentationOnSite B S hS
    𝒳.val.val.p 𝒳.val.isFiberedInGroupoids M.obj x (isAffine_point B S hS 𝒳 x e)
  let σ : (fppfStructurePresheaf B S hS 𝒳).obj (op x) →+* R := (pointRingIso B S hS 𝒳 x e).inv.hom
  have : RingHomSurjective σ := ⟨fun r => ⟨pointRingHom B S hS 𝒳 x e r,
    congrArg (fun φ : CommRingCat.of R ⟶ CommRingCat.of R => φ r)
      (pointRingIso B S hS 𝒳 x e).hom_inv_id⟩⟩
  let L : (modulesPresheaf B S hS 𝒳 M).obj (op x) →ₛₗ[σ] (pointPullback B S hS 𝒳 x e).obj M :=
    { toFun := fun m => m
      map_add' := fun _ _ => rfl
      map_smul' := fun γ m => congrArg
        (fun c => c • (show (modulesPresheaf B S hS 𝒳 M).obj (op x) from m))
        (congrArg (fun φ : (fppfStructurePresheaf B S hS 𝒳).obj (op x) ⟶
          (fppfStructurePresheaf B S hS 𝒳).obj (op x) => φ γ)
            (pointRingIso B S hS 𝒳 x e).inv_hom_id).symm }
  exact Module.Finite.of_surjective L (fun m => ⟨m, rfl⟩)

section OverSpec

variable {x} {hR : B.Contains (Spec (CommRingCat.of R))} {q : B.obj hR ⟶ B.obj hS}

/-- The identification `X_x ≅ Spec R` of the scheme under a point `x` with `p x = (Spec R → S)`. -/
def overSpecIso (hx : 𝒳.val.val.p.obj x = Over.mk q) :
    (BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x) ≅ Spec (CommRingCat.of R) :=
  eqToIso (congrArg (BigFppfOver.toScheme B S hS).obj hx)

/-- A 2-arrow between two points over `Spec R`, i.e. an isomorphism lying over the identity,
is compatible with the identifications `overSpecIso`. -/
theorem toScheme_map_comp_overSpecIso {y : 𝒳.val.val.obj} (hx : 𝒳.val.val.p.obj x = Over.mk q)
    (hy : 𝒳.val.val.p.obj y = Over.mk q) (a : x ≅ y)
    (ha : 𝒳.val.val.p.map a.hom = eqToHom (hx.trans hy.symm)) :
    (BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map a.hom) ≫
        (overSpecIso B S hS 𝒳 hy).hom = (overSpecIso B S hS 𝒳 hx).hom := by
  rw [ha, overSpecIso, overSpecIso, eqToIso.hom, eqToIso.hom, eqToHom_map, eqToHom_trans]

end OverSpec

end AlgebraicGeometry.Stack.AlgebraicStacks
