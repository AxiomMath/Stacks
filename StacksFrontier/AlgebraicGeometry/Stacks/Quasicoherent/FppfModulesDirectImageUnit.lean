module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.StackModuleDirectImageSections

/-!
# The unit of `f^* ⊣ f_*` on the fppf sites, at a terminal arrow

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks and `(x₀, f(x₀) ⟶ y)` a terminal object of
`CostructuredArrow f y`, so that `Γ(y, f_* N) ≅ Γ(x₀, N)` for every module `N` on `𝒳`.  For a
module `M` on `𝒴`, the unit `M ⟶ f_* f^* M` of the adjunction of **Stacks 06WE**, read through this
identification over `y`, is restriction of sections along the arrow `f(x₀) ⟶ y`:
`Γ(y, M) ⟶ Γ(f(x₀), M) = Γ(x₀, f^* M)`.

The library has two spellings of the fppf direct image and of its sections at a terminal arrow:
`AlgebraicGeometry.Stack.stackModuleDirectImageSectionsIsoOfIsTerminal` at `τ = fppf`, built from
the inverse image of `Stacks.RelativeCech`, and
`AlgebraicGeometry.Stack.fppfModulesPushforwardSectionsIsoOfIsTerminal`, built from
`AlgebraicGeometry.Stack.fppfModulesPullbackPushforwardAdjunction`.  They are equal: the two
identifications of the inverse images are one `eqToIso`.

## Main results

* `AlgebraicGeometry.Stack.stackModuleDirectImageIsoModuleDirectImage_fppf` and
  `AlgebraicGeometry.Stack.stackModuleDirectImageSectionsIsoOfIsTerminal_fppf`: the two spellings
  agree.
* `AlgebraicGeometry.Stack.fppfModulesPushforwardSectionsIsoOfIsTerminal_hom_app_unit`: the unit of
  `f^* ⊣ f_*` at a terminal arrow is restriction along it.

## References

* [Stacks Project, Tag 06WE](https://stacks.math.columbia.edu/tag/06WE)
* [Stacks Project, Tag 0GRP](https://stacks.math.columbia.edu/tag/0GRP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)

/-- The two identifications of the inverse image of modules on the fppf sites with
`AlgebraicGeometry.Stack.modulePullback` agree. -/
theorem stackModuleInverseImageIsoModulePullback_fppf :
    stackModuleInverseImageIsoModulePullback B S hS f .fppf =
      moduleInverseImageFppfIsoModulePullback.{u, w, u} B S hS f := rfl

/-- The adjunction `f^* ⊣ f_*` of `AlgebraicGeometry.Stack.stackModuleInverseDirectImageAdjunction`
at `τ = fppf`, transported to `AlgebraicGeometry.Stack.modulePullback`, is
`AlgebraicGeometry.Stack.fppfModulesPullbackPushforwardAdjunction`. -/
theorem stackModuleInverseDirectImageAdjunction_ofNatIsoLeft_fppf :
    (stackModuleInverseDirectImageAdjunction B S hS f .fppf).ofNatIsoLeft
      (stackModuleInverseImageIsoModulePullback B S hS f .fppf) =
      fppfModulesPullbackPushforwardAdjunction B S hS f := by
  rw [stackModuleInverseImageIsoModulePullback_fppf]
  rfl

/-- The two identifications of the fppf direct image with the canonical direct image
`AlgebraicGeometry.Stack.moduleDirectImage` agree. -/
theorem stackModuleDirectImageIsoModuleDirectImage_fppf :
    stackModuleDirectImageIsoModuleDirectImage B S hS f .fppf =
      fppfModulesPushforwardIsoModuleDirectImage B S hS f := by
  unfold stackModuleDirectImageIsoModuleDirectImage fppfModulesPushforwardIsoModuleDirectImage
  rw [stackModuleInverseDirectImageAdjunction_ofNatIsoLeft_fppf]
  rfl

/-- The two sections formulas for the fppf direct image at a terminal arrow agree. -/
theorem stackModuleDirectImageSectionsIsoOfIsTerminal_fppf {y : 𝒴.val.val.obj}
    {t : CostructuredArrow (CatFiberedInGroupoids.homFunctor f.hom) y} (ht : IsTerminal t) :
    stackModuleDirectImageSectionsIsoOfIsTerminal B S hS f .fppf ht =
      fppfModulesPushforwardSectionsIsoOfIsTerminal B S hS f ht := by
  unfold stackModuleDirectImageSectionsIsoOfIsTerminal
    fppfModulesPushforwardSectionsIsoOfIsTerminal
  rw [stackModuleDirectImageIsoModuleDirectImage_fppf]
  rfl

/-- The sections formula `Γ(y, f_* N) ≅ Γ(x₀, N)` is the comparison with the canonical direct
image followed by the leg of the right Kan extension at the terminal arrow. -/
theorem fppfModulesPushforwardSectionsIsoOfIsTerminal_hom_app_apply
    {y : 𝒴.val.val.obj} {t : CostructuredArrow (CatFiberedInGroupoids.homFunctor f.hom) y}
    (ht : IsTerminal t) (N : Stack.fppfModules B S hS 𝒳)
    (x : ((fppfModulesPushforward B S hS f).obj N).val.obj (op y)) :
    ((fppfModulesPushforwardSectionsIsoOfIsTerminal B S hS f ht).hom.app N).hom x =
      (Stacks.SheafOfModules.ranπ (CatFiberedInGroupoids.homFunctor f.hom).op N.val.presheaf (op y)
        (StructuredArrow.mk (Y := op t.left) t.hom.op)).hom
        ((((fppfModulesPushforwardIsoModuleDirectImage B S hS f).hom.app N).val.app (op y)).hom
          x) :=
  rfl

/-- **The unit of `f^* ⊣ f_*` at a terminal arrow is restriction along it.** For a terminal arrow
`(x₀, f(x₀) ⟶ y)` of `CostructuredArrow f y` and a module `M` on the fppf site of `𝒴`, the unit
`M ⟶ f_* f^* M` over `y`, read through `Γ(y, f_* f^* M) ≅ Γ(x₀, f^* M) = Γ(f(x₀), M)`, is the
restriction map of `M` along `f(x₀) ⟶ y`. -/
theorem fppfModulesPushforwardSectionsIsoOfIsTerminal_hom_app_unit
    (M : Stack.fppfModules B S hS 𝒴) {y : 𝒴.val.val.obj}
    {t : CostructuredArrow (CatFiberedInGroupoids.homFunctor f.hom) y} (ht : IsTerminal t)
    (z : M.val.obj (op y)) :
    ((fppfModulesPushforwardSectionsIsoOfIsTerminal B S hS f ht).hom.app
        ((fppfModulesPullback B S hS f).obj M)).hom
      ((((fppfModulesPullbackPushforwardAdjunction B S hS f).unit.app M).val.app (op y)).hom z) =
      (M.val.map t.hom.op).hom z := by
  have hu := Adjunction.unit_rightAdjointUniq_hom_app
    (fppfModulesPullbackPushforwardAdjunction B S hS f)
    (moduleDirectImageAdjunction.{u, u + 1, u, u + 1, u, u} B S hS 𝒳.val.val.p 𝒴.val.val.p
      𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
      (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
      B.topology le_rfl) M
  have h1 := congrArg (fun φ => (φ.val.app (op y)).hom z) hu
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.hom_comp,
    LinearMap.comp_apply] at h1
  have h2 := moduleDirectImageAdjunction_unit_app_ranπ.{u, u + 1, u, u + 1, u, u} B S hS
    𝒳.val.val.p 𝒴.val.val.p 𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
    (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
    B.topology le_rfl M (op y) (StructuredArrow.mk (Y := op t.left) t.hom.op)
  refine (fppfModulesPushforwardSectionsIsoOfIsTerminal_hom_app_apply B S hS f ht _ _).trans ?_
  unfold fppfModulesPushforwardIsoModuleDirectImage
  rw [h1]
  exact ConcreteCategory.congr_hom h2 z

end AlgebraicGeometry.Stack
