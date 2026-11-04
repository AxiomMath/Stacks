module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.PointPullback
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AffineMorphismTerminalArrow
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.QuasiCoherentModulesAndAffines
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FppfModulesBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.StackModuleDirectImageSections

/-!
# The quasi-coherent direct image along an affine 1-morphism, on sections over affine points

Let `f : 𝒳 ⟶ 𝒴` be an affine 1-morphism of algebraic stacks (Stacks 0CHQ) and `M` a
quasi-coherent `𝒪_𝒳`-module. The direct image `f_* M` of modules is again quasi-coherent: for
an arrow `y ⟶ y'` of `𝒴` between objects over affine schemes, the fibre products `y ×_𝒴 𝒳` and
`y' ×_𝒴 𝒳` are affine and the base-change comparison of `f_* M` is the one of `M` along the
induced arrow between them, which is an isomorphism because `M` is quasi-coherent; and a module on
`𝒴` which is cartesian between affine objects is quasi-coherent (Stacks 0H0E, condition (1),
read through the equivalence of Stacks 0H0C). Hence the coherator does nothing to `f_* M`, and
the quasi-coherent direct image `f_{QCoh,*} M = Q(f_* M)` of Stacks 077A is `f_* M` itself.

For an object `y` of `𝒴` over `Spec R` and the terminal arrow `(x₀, f(x₀) ⟶ y)` of
`CostructuredArrow f y` (the fibre product `y ×_𝒴 𝒳`), the `R`-module `y^*(f_{QCoh,*} M)` of
`AlgebraicGeometry.Stack.AlgebraicStacks.pointPullback` is therefore the module of sections
`M(x₀)`, with `R` acting through `R ≅ Γ(y, 𝒪) ⟶ Γ(x₀, 𝒪)`. This is the identification
`C = f^*(g_{QCoh,*} 𝒪_U)` of the coordinate ring of `Spec B ×_𝒳 U` used in the proofs of
Stacks 0GRP and 0GRQ.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.affineQuasicoherentDirectImage`: `f_*` as a functor
  `QCoh(𝒪_𝒳) ⥤ QCoh(𝒪_𝒴)` for an affine `f`, and
  `AlgebraicGeometry.Stack.AlgebraicStacks.affineQuasicoherentDirectImageIso`, its
  identification with `f_{QCoh,*}`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.pointPullbackQuasicoherentDirectImageAddEquiv`: the
  identification `y^*(f_{QCoh,*} M) ≃ M(x₀)`, semilinear along `terminalArrowRingHom`.

## Main results

* `AlgebraicGeometry.Stack.AffineCategory.isQuasicoherentOnSite_of_isIso_restrictionBaseChange`:
  a module on the fppf site of a category fibred in groupoids which is cartesian between affine
  objects is quasi-coherent.
* `AlgebraicStacks.isQuasicoherentOnSite_fppfModulesPushforward_of_isAffineHom`:
  the direct image of a quasi-coherent module along an affine 1-morphism is quasi-coherent.
* `Stacks.SheafOfModules.pushforwardCocontinuousSectionsIsoOfIsTerminal_hom_app_smul` and
  `AlgebraicStacks.stackModuleDirectImageSectionsIsoOfIsTerminal_hom_app_smul`:
  the sections formula `Γ(y, f_* M) ≅ Γ(x₀, M)` is semilinear along `Γ(y, 𝒪) ⟶ Γ(x₀, 𝒪)`.

## References

* [Stacks Project, Tag 0GRP](https://stacks.math.columbia.edu/tag/0GRP)
* [Stacks Project, Tag 0GRK](https://stacks.math.columbia.edu/tag/0GRK)
* [Stacks Project, Tag 077A](https://stacks.math.columbia.edu/tag/077A)
* [Stacks Project, Tag 0H0E](https://stacks.math.columbia.edu/tag/0H0E)
* [Stacks Project, Tag 0CHQ](https://stacks.math.columbia.edu/tag/0CHQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

section Leg

universe v' w' m r

namespace Stacks.SheafOfModules

variable {X : Type v} [Category.{w} X] {Y : Type v'} [Category.{w'} Y] {F : X ⥤ Y}
  {JX : GrothendieckTopology X} {JY : GrothendieckTopology Y} [F.IsCocontinuous JX JY]
  [∀ G : Xᵒᵖ ⥤ RingCat.{r}, F.op.HasPointwiseRightKanExtension G]
  [∀ G : Xᵒᵖ ⥤ AddCommGrpCat.{m}, F.op.HasPointwiseRightKanExtension G]
  {OX : Sheaf JX RingCat.{r}} {OY : Sheaf JY RingCat.{r}}
  (fSharp : OY ⟶ (F.sheafPushforwardCocontinuous RingCat.{r} JX JY).obj OX)
  {y : Y} {t : CostructuredArrow F y} (ht : IsTerminal t)

/-- **The sections formula of a direct image at a terminal arrow is semilinear**: the leg
`Γ(y, f_* M) ⟶ Γ(x₀, M)` carries `s • m` to `f^♯(s) • m`, `f^♯ : 𝒪_Y(y) ⟶ 𝒪_X(x₀)` being the
ring map cut out by the structure map at that leg. -/
theorem pushforwardCocontinuousSectionsIsoOfIsTerminal_hom_app_smul
    (M : _root_.SheafOfModules.{m} OX) (s : OY.obj.obj (op y))
    (x : ((pushforwardCocontinuous.{m} F fSharp).obj M).val.obj (op y)) :
    ((pushforwardCocontinuousSectionsIsoOfIsTerminal fSharp ht).hom.app M).hom (s • x) =
      ((scalarπ F (structureMapPresheaf F fSharp) (op y)
        (StructuredArrow.mk (Y := op t.left) t.hom.op)).hom s : OX.obj.obj (op t.left)) •
        (show M.val.obj (op t.left) from
          ((pushforwardCocontinuousSectionsIsoOfIsTerminal fSharp ht).hom.app M).hom x) :=
  ConcreteCategory.congr_hom (ranSMul_π F (structureMapPresheaf F fSharp) M.val (op y) s _) x

end Stacks.SheafOfModules
end Leg

namespace AlgebraicGeometry.Stack.AffineCategory

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- **A module cartesian between affine objects is quasi-coherent.** A sheaf of modules on the
fppf site of a category fibred in groupoids `p : 𝒳 ⥤ (Sch/S)_{fppf}` whose base-change maps
`Γ(y) ⊗_{Γ(y')} M(y') ⟶ M(y)` are isomorphisms along every arrow `y ⟶ y'` between objects over
affine schemes is quasi-coherent: its restriction to the affine subcategory is quasi-coherent by
condition (1) of Stacks 0H0E, and quasi-coherence reflects along the dense subsite inclusion. -/
theorem isQuasicoherentOnSite_of_isIso_restrictionBaseChange
    (M : SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS p hp .fppf))
    (h : ∀ ⦃y y' : 𝒳⦄ (f : y ⟶ y'),
      IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj y)) →
      IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj y')) →
      IsIso (Stacks.PresheafOfModules.restrictionBaseChange.{v, w, u, u}
        (R := (FibredSite.structureSheaf B S hS p hp .fppf).obj) M.val f.op)) :
    M.IsQuasicoherentOnSite := by
  let := isDenseSubsite_inclusion_siteKind B S hS p hp .fppf
  refine isQuasicoherentOnSite_of_moduleRestriction B S hS p
    (siteKindRingedSite B S hS p hp .fppf).J (BigFppfOver.associatedTopology B S hS p .fppf) hp
    _ M ?_
  exact Stacks.SheafOfModules.isQuasicoherentOnSite_of_canonicalMap_isIso
    (siteKindRingedSite B S hS p hp .fppf) _ fun x x' f => h ((inclusion B S hS p).map f) x.2 x'.2

end AlgebraicGeometry.Stack.AffineCategory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The direct image along an affine 1-morphism of a quasi-coherent module is quasi-coherent.**
It is cartesian between affine objects, because the arrow between the fibre products over an
arrow of affine objects is an arrow between affine objects along which `M` is cartesian. -/
theorem isQuasicoherentOnSite_fppfModulesPushforward_of_isAffineHom
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (hf : IsAffineHom B S hS f)
    (M : quasicoherentModules B S hS 𝒳) :
    ((fppfModulesPushforward B S hS f).obj M.obj).IsQuasicoherentOnSite :=
  AffineCategory.isQuasicoherentOnSite_of_isIso_restrictionBaseChange B S hS 𝒴.val.val.p
    𝒴.val.isFiberedInGroupoids _ fun _ _ φ hy hy' =>
      isIso_restrictionBaseChange_stackModuleDirectImage_of_isAffineHom B S hS ⊤ .fppf f hf M.obj
        (fun _ _ ψ hx hx' _ => FibredSite.isIso_restrictionBaseChange_of_isQuasicoherentOnSite
          M.obj M.property ψ hx hx') φ hy hy' trivial

variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (hf : IsAffineHom B S hS f)

/-- **The sections formula `Γ(y, f_* M) ≅ Γ(x₀, M)` at a terminal arrow `f(x₀) ⟶ y` is
semilinear** along restriction of functions along that arrow, `Γ(y, 𝒪) ⟶ Γ(x₀, 𝒪)`. -/
theorem stackModuleDirectImageSectionsIsoOfIsTerminal_hom_app_smul (τ : SiteKind)
    {y : 𝒴.val.val.obj} {t : CostructuredArrow (CatFiberedInGroupoids.homFunctor f.hom) y}
    (ht : IsTerminal t) (M : StackModules B S hS τ 𝒳)
    (s : (ringStructureSheafCore B S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids
      (B.baseTopology τ) (B.baseTopology_le_topology τ)).obj.obj (op y))
    (x : ((stackModuleDirectImage B S hS f τ).obj M).val.obj (op y)) :
    ((stackModuleDirectImageSectionsIsoOfIsTerminal B S hS f τ ht).hom.app M).hom (s • x) =
      (((ringStructureSheafCore B S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids
          (B.baseTopology τ) (B.baseTopology_le_topology τ)).obj.map t.hom.op ≫
        (eqToHom (ringStructureSheafCore_obj_eq B S hS 𝒳.val.val.p 𝒴.val.val.p
          𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
          (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
          (B.baseTopology τ) (B.baseTopology_le_topology τ)).symm).app (op t.left)).hom s :
          (ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
            (B.baseTopology τ) (B.baseTopology_le_topology τ)).obj.obj (op t.left)) •
        (show M.val.obj (op t.left) from
          ((stackModuleDirectImageSectionsIsoOfIsTerminal B S hS f τ ht).hom.app M).hom x) := by
  change ((Stacks.SheafOfModules.pushforwardCocontinuousSectionsIsoOfIsTerminal
      (moduleDirectImageStructureMap B S hS 𝒳.val.val.p 𝒴.val.val.p 𝒳.val.isFiberedInGroupoids
        𝒴.val.isFiberedInGroupoids (CatFiberedInGroupoids.homFunctor f.hom)
        (CatFiberedInGroupoids.homFunctor_comp_p f.hom) (B.baseTopology τ)
        (B.baseTopology_le_topology τ)) ht).hom.app _).hom
      ((((stackModuleDirectImageIsoModuleDirectImage B S hS f τ).hom.app M).val.app
        (op y)).hom (s • x)) = _
  rw [LinearMap.map_smul,
    Stacks.SheafOfModules.pushforwardCocontinuousSectionsIsoOfIsTerminal_hom_app_smul,
    Stacks.SheafOfModules.structureMapPresheaf, scalarπ_moduleDirectImageStructureMap]
  rfl

/-- The direct image of modules along an affine 1-morphism, as a functor
`QCoh(𝒪_𝒳) ⥤ QCoh(𝒪_𝒴)`. -/
def affineQuasicoherentDirectImage :
    quasicoherentModules B S hS 𝒳 ⥤ quasicoherentModules B S hS 𝒴 :=
  ObjectProperty.lift _ (quasicoherentInclusion B S hS 𝒳 ⋙ fppfModulesPushforward B S hS f)
    (isQuasicoherentOnSite_fppfModulesPushforward_of_isAffineHom B S hS f hf)

/-- **For an affine 1-morphism the quasi-coherent direct image is the direct image**: the
coherator is the identity on the quasi-coherent module `f_* M`. -/
def affineQuasicoherentDirectImageIso :
    quasicoherentDirectImage B S hS f ≅ affineQuasicoherentDirectImage B S hS f hf :=
  Functor.isoWhiskerLeft (affineQuasicoherentDirectImage B S hS f hf)
    (asIso (coheratorAdjunction B S hS 𝒴).unit).symm

variable {R : Type u} [CommRing R] {y : 𝒴.val.val.obj}
  (e : (BigFppfOver.toScheme B S hS).obj (𝒴.val.val.p.obj y) ≅ Spec (CommRingCat.of R))
  {t : CostructuredArrow (CatFiberedInGroupoids.homFunctor f.hom) y} (ht : IsTerminal t)

/-- The ring map `Γ(y, 𝒪_𝒴) ⟶ Γ(x₀, 𝒪_𝒳)` of restriction of functions along an arrow
`f(x₀) ⟶ y`. -/
def terminalArrowRingHom (t : CostructuredArrow (CatFiberedInGroupoids.homFunctor f.hom) y) :
    (ringStructureSheafCore B S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids
      (B.baseTopology .fppf) (B.baseTopology_le_topology .fppf)).obj.obj (op y) →+*
    (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
      .fppf).obj.obj (op t.left) :=
  ((ringStructureSheafCore B S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids
          (B.baseTopology .fppf) (B.baseTopology_le_topology .fppf)).obj.map t.hom.op ≫
        (eqToHom (ringStructureSheafCore_obj_eq B S hS 𝒳.val.val.p 𝒴.val.val.p
          𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
          (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
          (B.baseTopology .fppf) (B.baseTopology_le_topology .fppf)).symm).app (op t.left)).hom

/-- **The pullback of `f_{QCoh,*} M` to a point over `Spec R` is the module of sections of `M`
over the fibre product**: for the terminal arrow `(x₀, f(x₀) ⟶ y)`, `y^*(f_{QCoh,*} M) ≃ M(x₀)`
as abelian groups, semilinearly along `R ⟶ Γ(y, 𝒪) ⟶ Γ(x₀, 𝒪)`
(`pointPullbackQuasicoherentDirectImageAddEquiv_smul`), naturally in `M`. -/
def pointPullbackQuasicoherentDirectImageAddEquiv (M : quasicoherentModules B S hS 𝒳) :
    (pointPullback B S hS 𝒴 y e).obj ((quasicoherentDirectImage B S hS f).obj M) ≃+
      M.obj.val.obj (op t.left) :=
  ((pointPullback B S hS 𝒴 y e).mapIso
      ((affineQuasicoherentDirectImageIso B S hS f hf).app M)).toLinearEquiv.toAddEquiv.trans
    ((stackModuleDirectImageSectionsIsoOfIsTerminal B S hS f .fppf ht).app
      M.obj).addCommGroupIsoToAddEquiv

/-- The identification `y^*(f_{QCoh,*} M) ≃ M(x₀)` is semilinear along
`R ⟶ Γ(y, 𝒪) ⟶ Γ(x₀, 𝒪)`. -/
theorem pointPullbackQuasicoherentDirectImageAddEquiv_smul (M : quasicoherentModules B S hS 𝒳)
    (r : R)
    (m : (pointPullback B S hS 𝒴 y e).obj ((quasicoherentDirectImage B S hS f).obj M)) :
    pointPullbackQuasicoherentDirectImageAddEquiv B S hS f hf e ht M (r • m) =
      terminalArrowRingHom B S hS f t (pointRingHom B S hS 𝒴 y e r) •
        pointPullbackQuasicoherentDirectImageAddEquiv B S hS f hf e ht M m := by
  change ((stackModuleDirectImageSectionsIsoOfIsTerminal B S hS f .fppf ht).hom.app M.obj).hom
      (((pointPullback B S hS 𝒴 y e).map
        ((affineQuasicoherentDirectImageIso B S hS f hf).hom.app M)).hom (r • m)) = _
  rw [LinearMap.map_smul]
  exact stackModuleDirectImageSectionsIsoOfIsTerminal_hom_app_smul B S hS f .fppf ht M.obj
    (pointRingHom B S hS 𝒴 y e r) _

/-- The identification `y^*(f_{QCoh,*} M) ≃ M(x₀)` is natural in `M`. -/
theorem pointPullbackQuasicoherentDirectImageAddEquiv_naturality
    {M N : quasicoherentModules B S hS 𝒳}
    (φ : M ⟶ N)
    (m : (pointPullback B S hS 𝒴 y e).obj ((quasicoherentDirectImage B S hS f).obj M)) :
    pointPullbackQuasicoherentDirectImageAddEquiv B S hS f hf e ht N
        ((pointPullback B S hS 𝒴 y e).map ((quasicoherentDirectImage B S hS f).map φ) m) =
      (φ.hom.val.app (op t.left)).hom
        (pointPullbackQuasicoherentDirectImageAddEquiv B S hS f hf e ht M m) := by
  have h1 := congrArg (fun k => ((pointPullback B S hS 𝒴 y e).map k).hom m)
    ((affineQuasicoherentDirectImageIso B S hS f hf).hom.naturality φ)
  simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at h1
  have h2 := ConcreteCategory.congr_hom
    ((stackModuleDirectImageSectionsIsoOfIsTerminal B S hS f .fppf ht).hom.naturality φ.hom)
    (((pointPullback B S hS 𝒴 y e).map
      ((affineQuasicoherentDirectImageIso B S hS f hf).hom.app M)).hom m)
  change ((stackModuleDirectImageSectionsIsoOfIsTerminal B S hS f .fppf ht).hom.app N.obj).hom
      (((pointPullback B S hS 𝒴 y e).map
        ((affineQuasicoherentDirectImageIso B S hS f hf).hom.app N)).hom
          (((pointPullback B S hS 𝒴 y e).map
            ((quasicoherentDirectImage B S hS f).map φ)).hom m)) = _
  rwa [h1]

end AlgebraicGeometry.Stack.AlgebraicStacks

end
