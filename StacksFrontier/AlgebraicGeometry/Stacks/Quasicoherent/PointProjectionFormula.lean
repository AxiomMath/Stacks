module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AffineProjectionFormula

/-!
# The projection formula for an affine 1-morphism, read at a point

Let `g : 𝒰 ⟶ 𝒳` be an affine 1-morphism of algebraic stacks, `M` a quasi-coherent
`𝒪_𝒳`-module, and `y` an object of `𝒳` over `Spec R`, with terminal arrow `(x₀, g x₀ ⟶ y)`
(`x₀ = U ×_𝒳 y` for a scheme `U`). Reading the projection formula
`M ⊗ g_{QCoh,*}𝒪_𝒰 ≅ g_{QCoh,*}g^*M`
(`AlgebraicGeometry.Stack.AlgebraicStacks.projectionFormulaIso`) at `y`, and the pullback of a
direct image at `y` as sections over `x₀`
(`AlgebraicGeometry.Stack.AlgebraicStacks.pointPullbackQuasicoherentDirectImageAddEquiv`), gives

`y^*(M ⊗ g_{QCoh,*}𝒪_𝒰) ≃ (g^*M)(x₀) = M(g x₀)`,

semilinear along `R ⟶ Γ(y, 𝒪) ⟶ Γ(x₀, 𝒪)` and natural in `M`. Composed with the tensorator of
the monoidal functor `y^*`, it identifies `y^*M ⊗_R y^*(g_{QCoh,*}𝒪_𝒰)` with `M(g x₀)`, where
`y^*(g_{QCoh,*}𝒪_𝒰) ≃ Γ(x₀, 𝒪_𝒰)` by the same identification at the unit: this is the shape
`F(M ⊗ g_*𝒪) ≅ F(M) ⊗ Γ(x₀)` of step 5 of the proof of Stacks 0GRQ for `F = y^*`.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.pointPullbackProjectionAddEquiv`:
  `y^*(M ⊗ g_{QCoh,*}𝒪_𝒰) ≃+ (g^*M)(x₀)`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.pointPullbackTensorProjectionAddEquiv`:
  `y^*M ⊗_R y^*(g_{QCoh,*}𝒪_𝒰) ≃+ (g^*M)(x₀)`.

## References

* [Stacks Project, Tag 0GRQ](https://stacks.math.columbia.edu/tag/0GRQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

attribute [local instance] fppfModulesMonoidal fppfModulesBraided fppfModulesSymmetric

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒰 𝒳 : AlgebraicStacks.{u, w} B S hS} {g : 𝒰 ⟶ 𝒳} (hg : IsAffineHom B S hS g)
  {R : Type u} [CommRing R] {y : 𝒳.val.val.obj}
  (e : (BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj y) ≅ Spec (CommRingCat.of R))
  {t : CostructuredArrow (CatFiberedInGroupoids.homFunctor g.hom) y} (ht : IsTerminal t)

/-- **The projection formula at a point**: for `g` affine, `y` over `Spec R` and `(x₀, g x₀ ⟶ y)`
the terminal arrow, `y^*(M ⊗ g_{QCoh,*}𝒪_𝒰) ≃ (g^*M)(x₀) = M(g x₀)` as abelian groups: the
projection formula `projectionFormulaIso` at `y`, followed by
`pointPullbackQuasicoherentDirectImageAddEquiv` for `g^*M`. -/
def pointPullbackProjectionAddEquiv (M : quasicoherentModules B S hS 𝒳) :
    (pointPullback B S hS 𝒳 y e).obj (M ⊗ (quasicoherentDirectImage B S hS g).obj (𝟙_ _)) ≃+
      ((quasicoherentPullback B S hS g).obj M).obj.val.obj (op t.left) :=
  ((pointPullback B S hS 𝒳 y e).mapIso
      ((projectionFormulaIso hg).app M)).toLinearEquiv.toAddEquiv.trans
    (pointPullbackQuasicoherentDirectImageAddEquiv B S hS g hg e ht
      ((quasicoherentPullback B S hS g).obj M))

/-- The projection formula at a point is `projectionFormulaIso` at `y`, followed by
`pointPullbackQuasicoherentDirectImageAddEquiv` for `g^*M`. -/
theorem pointPullbackProjectionAddEquiv_apply (M : quasicoherentModules B S hS 𝒳)
    (z : (pointPullback B S hS 𝒳 y e).obj
      (M ⊗ (quasicoherentDirectImage B S hS g).obj (𝟙_ _))) :
    pointPullbackProjectionAddEquiv hg e ht M z =
      pointPullbackQuasicoherentDirectImageAddEquiv B S hS g hg e ht
        ((quasicoherentPullback B S hS g).obj M)
        (((pointPullback B S hS 𝒳 y e).map ((projectionFormulaIso hg).hom.app M)).hom z) :=
  rfl

/-- The projection formula at a point is semilinear along `R ⟶ Γ(y, 𝒪) ⟶ Γ(x₀, 𝒪)`. -/
theorem pointPullbackProjectionAddEquiv_smul (M : quasicoherentModules B S hS 𝒳) (r : R)
    (z : (pointPullback B S hS 𝒳 y e).obj
      (M ⊗ (quasicoherentDirectImage B S hS g).obj (𝟙_ _))) :
    pointPullbackProjectionAddEquiv hg e ht M (r • z) =
      terminalArrowRingHom B S hS g t (pointRingHom B S hS 𝒳 y e r) •
        pointPullbackProjectionAddEquiv hg e ht M z := by
  change pointPullbackQuasicoherentDirectImageAddEquiv B S hS g hg e ht
      ((quasicoherentPullback B S hS g).obj M)
      (((pointPullback B S hS 𝒳 y e).map ((projectionFormulaIso hg).hom.app M)).hom (r • z)) = _
  rw [LinearMap.map_smul]
  exact pointPullbackQuasicoherentDirectImageAddEquiv_smul B S hS g hg e ht _ r _

/-- The projection formula at a point is natural in `M`. -/
theorem pointPullbackProjectionAddEquiv_naturality {M N : quasicoherentModules B S hS 𝒳}
    (φ : M ⟶ N)
    (z : (pointPullback B S hS 𝒳 y e).obj
      (M ⊗ (quasicoherentDirectImage B S hS g).obj (𝟙_ _))) :
    pointPullbackProjectionAddEquiv hg e ht N
        ((pointPullback B S hS 𝒳 y e).map (φ ▷ (quasicoherentDirectImage B S hS g).obj (𝟙_ _))
          z) =
      (((quasicoherentPullback B S hS g).map φ).hom.val.app (op t.left)).hom
        (pointPullbackProjectionAddEquiv hg e ht M z) := by
  have h := congrArg (fun k => ((pointPullback B S hS 𝒳 y e).map k).hom z)
    ((projectionFormulaIso hg).hom.naturality φ)
  simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at h
  rw [pointPullbackProjectionAddEquiv_apply, pointPullbackProjectionAddEquiv_apply]
  rw [show (tensorRight ((quasicoherentDirectImage B S hS g).obj (𝟙_ _))).map φ =
    φ ▷ (quasicoherentDirectImage B S hS g).obj (𝟙_ _) from rfl] at h
  rw [h]
  exact pointPullbackQuasicoherentDirectImageAddEquiv_naturality B S hS g hg e ht _ _

/-- **The projection formula at a point, in tensor form**: `y^*M ⊗_R y^*(g_{QCoh,*}𝒪_𝒰) ≃
(g^*M)(x₀)`, the tensorator of the monoidal functor `y^*` followed by
`pointPullbackProjectionAddEquiv`. The second factor is `Γ(x₀, 𝒪_𝒰)` by
`pointPullbackQuasicoherentDirectImageAddEquiv` at the unit. -/
def pointPullbackTensorProjectionAddEquiv (M : quasicoherentModules B S hS 𝒳) :
    TensorProduct R ((pointPullback B S hS 𝒳 y e).obj M)
        ((pointPullback B S hS 𝒳 y e).obj ((quasicoherentDirectImage B S hS g).obj (𝟙_ _))) ≃+
      ((quasicoherentPullback B S hS g).obj M).obj.val.obj (op t.left) :=
  (Functor.Monoidal.μIso (pointPullback B S hS 𝒳 y e) M
      ((quasicoherentDirectImage B S hS g).obj (𝟙_ _))).toLinearEquiv.toAddEquiv.trans
    (pointPullbackProjectionAddEquiv hg e ht M)

end AlgebraicGeometry.Stack.AlgebraicStacks
