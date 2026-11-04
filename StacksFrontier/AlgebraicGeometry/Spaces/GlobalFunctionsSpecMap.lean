module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProperGlobalFunctionsIntegral

/-!
# The morphism to an affine scheme attached to an algebra map into the global functions

Let `X` be an algebraic space over the spectrum of a ring `R`, and let `A` be an `R`-algebra
whose spectrum lies in the chosen big fppf site.  An `R`-algebra homomorphism
`φ : A ⟶ Γ(X, 𝒪_X)` gives a morphism of algebraic spaces `X ⟶ Spec A` *over* `Spec R`.

## Main definitions

* `AlgebraicGeometry.Space.globalFunctionsChartEval`: the value of a global regular function
  of `X` at an arbitrary scheme chart `x ∈ X(W)`, not only at an étale one.
* `AlgebraicGeometry.Space.specSiteObject`: the spectrum of an `R`-algebra, as an object of
  the big fppf site over `Spec R`.
* `AlgebraicGeometry.Space.toSpecOfAlgHom`: the morphism `X ⟶ Spec A` over `Spec R` attached
  to an `R`-algebra homomorphism `A ⟶ Γ(X, 𝒪_X)`.

## Implementation notes

Stacks 05Z1, `AlgebraicGeometry.Space.morphismToAffineEquiv`, is the bijection between such
morphisms and ring homomorphisms, over a *terminal* base;  over the base `Spec R` the
compatibility of the chart morphisms with the structure morphisms to `Spec R` is not automatic,
and is what the `R`-linearity of `φ` supplies.  Only the morphism is built here, not the
bijection: on a scheme chart `x ∈ X(W)` it is the morphism `W ⟶ Spec A` of the composite
`A ⟶ Γ(X, 𝒪_X) ⟶ Γ(W, 𝒪_W)`, and the values of global functions on arbitrary scheme charts are
those of `AlgebraicGeometry.Space.globalFunctionsChartEquiv`, which is where algebraicity of `X`
enters.

## References

* [Stacks Project, Tag 05Z1](https://stacks.math.columbia.edu/tag/05Z1)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

/-! ### Values of global functions on arbitrary scheme charts -/

section Chart

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-- The scheme chart of a presheaf on the big fppf site attached to a section `x ∈ X(W)`. -/
abbrev sectionChart {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (W : BigFppfOver B S hS)
    (x : F.obj (op W)) : CostructuredArrow yoneda F :=
  CostructuredArrow.mk (yonedaEquiv.symm x)

/-- **The value of a global regular function at a scheme chart.**  A section `x ∈ X(W)` is a
scheme chart `W ⟶ X`, not necessarily étale, and a global regular function of the algebraic
space `X` has a value on it, by `AlgebraicGeometry.Space.globalFunctionsChartEquiv`. -/
def globalFunctionsChartEval (W : BigFppfOver B S hS) (x : X.obj.obj (op W)) :
    globalFunctions B S hS X.obj →+* Γ((BigFppfOver.toScheme B S hS).obj W, ⊤) where
  toFun s := ((globalFunctionsChartEquiv B S hS X).val s).val (op (sectionChart B S hS W x))
  map_one' := by rw [map_one]; rfl
  map_mul' a b := by rw [map_mul]; rfl
  map_zero' := by rw [map_zero]; rfl
  map_add' a b := by rw [map_add]; rfl

/-- The values of a global function on scheme charts are compatible with morphisms of the site:
pulling back the value at `x ∈ X(W)` along `g : W' ⟶ W` gives the value at `X(g)(x)`. -/
theorem globalFunctionsChartEval_map {W W' : BigFppfOver B S hS} (g : W' ⟶ W)
    (x : X.obj.obj (op W)) (s : globalFunctions B S hS X.obj) :
    (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map g).op).hom
        (globalFunctionsChartEval B S hS X W x s) =
      globalFunctionsChartEval B S hS X W' (X.obj.map g.op x) s := by
  let h : sectionChart B S hS W' (X.obj.map g.op x) ⟶ sectionChart B S hS W x :=
    CostructuredArrow.homMk g (by
      change yoneda.map g ≫ yonedaEquiv.symm x = yonedaEquiv.symm (X.obj.map g.op x)
      rw [yonedaEquiv_symm_naturality_left])
  exact ((globalFunctionsChartEquiv B S hS X).val s).property h.op

/-- The restriction of the all-chart family of a global function to the étale charts is that
function. -/
theorem globalFunctionsChartEval_chart (U : SmallEtale B S hS X.obj)
    (s : globalFunctions B S hS X.obj) :
    globalFunctionsChartEval B S hS X U.obj.left (yonedaEquiv U.obj.hom) s = s.val (op U) := by
  have h := congrArg (fun t : globalFunctions' B S hS X.obj => t.val (op U))
    ((globalFunctionsChartEquiv B S hS X).property s)
  let f : (SmallEtale.inclusion B S hS X.obj).obj U ⟶
      sectionChart B S hS U.obj.left (yonedaEquiv U.obj.hom) :=
    CostructuredArrow.homMk (𝟙 _) (by simp)
  have hf := ((globalFunctionsChartEquiv B S hS X).val s).property f.op
  refine Eq.trans ?_ (h.trans rfl)
  refine Eq.trans ?_ hf
  change _ = (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (𝟙 _)).op).hom _
  rfl

end Chart

/-! ### Constants on scheme charts -/

section Base

variable (R : Type u) [CommRing R] (B : BigFppfSite.{u}) (hR : B.Contains (Spec (.of R)))
    (X : AlgebraicSpaces B (Spec (.of R)) hR)

/-- **The value of a constant at a scheme chart is its pullback along the structure morphism of
the chart.**  The family of these pullbacks is
`AlgebraicGeometry.Space.baseToChartFunctions`;  it restricts on the étale charts to
`AlgebraicGeometry.Space.baseToGlobalFunctions`, and restriction to the étale charts is
injective on an algebraic space. -/
theorem globalFunctionsChartEval_baseToGlobalFunctions (W : BigFppfOver B (Spec (.of R)) hR)
    (x : X.obj.obj (op W)) (a : R) :
    globalFunctionsChartEval B (Spec (.of R)) hR X W x (baseToGlobalFunctions R B hR X.obj a) =
      ((Scheme.ΓSpecIso (.of R)).inv ≫ Scheme.Γ.map (B.inclusion.map W.hom).op).hom a := by
  have hc : (globalFunctionsChartEquiv B (Spec (.of R)) hR X).val
      (baseToGlobalFunctions R B hR X.obj a) = baseToChartFunctions R B hR X.obj a := by
    apply chartFunctionsToSmall_injective B (Spec (.of R)) hR X.obj X.property
    rw [(globalFunctionsChartEquiv B (Spec (.of R)) hR X).property,
      chartFunctionsToSmall_baseToChartFunctions]
  change ((globalFunctionsChartEquiv B (Spec (.of R)) hR X).val
    (baseToGlobalFunctions R B hR X.obj a)).val _ = _
  rw [hc]
  rfl

/-! ### The morphism to the spectrum of an algebra -/

variable (A : Type u) [CommRing A] [Algebra R A] (hA : B.Contains (Spec (.of A)))

/-- The spectrum of an `R`-algebra whose spectrum lies in the chosen big fppf site, as an object
of that site over `Spec R` through the structure morphism of the algebra. -/
def specSiteObject : BigFppfOver B (Spec (.of R)) hR :=
  Over.mk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap R A))) :
    B.obj hA ⟶ B.obj hR)

/-- The underlying scheme of `AlgebraicGeometry.Space.specSiteObject`, which is `Spec A`, is
affine. -/
instance isAffine_specSiteObject :
    IsAffine ((BigFppfOver.toScheme B (Spec (.of R)) hR).obj (specSiteObject R B hR A hA)) :=
  isAffine_Spec (CommRingCat.of A)

variable (φ : A →ₐ[R] globalFunctions B (Spec (.of R)) hR X.obj)

/-- The morphism of schemes `W ⟶ Spec A` attached to a scheme chart `x ∈ X(W)`:  the morphism of
the ring homomorphism `A ⟶ Γ(X, 𝒪_X) ⟶ Γ(W, 𝒪_W)`. -/
def toSpecOfAlgHomChart (W : BigFppfOver B (Spec (.of R)) hR) (x : X.obj.obj (op W)) :
    (BigFppfOver.toScheme B (Spec (.of R)) hR).obj W ⟶ Spec (.of A) :=
  ((BigFppfOver.toScheme B (Spec (.of R)) hR).obj W).toSpecΓ ≫
    Spec.map (CommRingCat.ofHom
      ((globalFunctionsChartEval B (Spec (.of R)) hR X W x).comp φ.toRingHom))

/-- The chart morphism of `AlgebraicGeometry.Space.toSpecOfAlgHomChart` is a morphism over
`Spec R`, because `φ` is `R`-linear and constants have the expected values on charts. -/
theorem toSpecOfAlgHomChart_comp (W : BigFppfOver B (Spec (.of R)) hR)
    (x : X.obj.obj (op W)) :
    toSpecOfAlgHomChart R B hR X A φ W x ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      B.inclusion.map W.hom := by
  have hring : CommRingCat.ofHom (algebraMap R A) ≫ CommRingCat.ofHom
      ((globalFunctionsChartEval B (Spec (.of R)) hR X W x).comp φ.toRingHom) =
      (Scheme.ΓSpecIso (.of R)).inv ≫ (B.inclusion.map W.hom).appTop := by
    ext a
    change globalFunctionsChartEval B (Spec (.of R)) hR X W x (φ (algebraMap R A a)) = _
    rw [φ.commutes, algebraMap_globalFunctions,
      globalFunctionsChartEval_baseToGlobalFunctions]
    rfl
  rw [toSpecOfAlgHomChart, Category.assoc, ← Spec.map_comp, hring, Spec.map_comp,
    ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc]
  change _ ≫ (Spec (.of R)).toSpecΓ ≫ _ = _
  rw [toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

/-- The chart morphisms of `AlgebraicGeometry.Space.toSpecOfAlgHomChart` are compatible with
morphisms of the site. -/
theorem toSpecOfAlgHomChart_naturality {W W' : BigFppfOver B (Spec (.of R)) hR} (g : W' ⟶ W)
    (x : X.obj.obj (op W)) :
    (BigFppfOver.toScheme B (Spec (.of R)) hR).map g ≫ toSpecOfAlgHomChart R B hR X A φ W x =
      toSpecOfAlgHomChart R B hR X A φ W' (X.obj.map g.op x) := by
  rw [toSpecOfAlgHomChart, ← Category.assoc, Scheme.toSpecΓ_naturality, Category.assoc,
    ← Spec.map_comp, toSpecOfAlgHomChart]
  congr 2
  ext s
  exact globalFunctionsChartEval_map B (Spec (.of R)) hR X g x (φ s)

/-- The morphism of the site `W ⟶ Spec A` over `Spec R` attached to a scheme chart. -/
def toSpecOfAlgHomApp (W : BigFppfOver B (Spec (.of R)) hR) (x : X.obj.obj (op W)) :
    W ⟶ specSiteObject R B hR A hA :=
  let g : (BigFppfOver.toScheme B (Spec (.of R)) hR).obj W ⟶
      (BigFppfOver.toScheme B (Spec (.of R)) hR).obj (specSiteObject R B hR A hA) :=
    toSpecOfAlgHomChart R B hR X A φ W x
  Over.homMk (B.inclusion.preimage g)
    (B.inclusion.map_injective (by
      rw [B.inclusion.map_comp, B.inclusion.map_preimage]
      exact toSpecOfAlgHomChart_comp R B hR X A φ W x))

/-- The morphism of schemes underlying `AlgebraicGeometry.Space.toSpecOfAlgHomApp` is
`AlgebraicGeometry.Space.toSpecOfAlgHomChart`. -/
theorem toScheme_map_toSpecOfAlgHomApp (W : BigFppfOver B (Spec (.of R)) hR)
    (x : X.obj.obj (op W)) :
    (BigFppfOver.toScheme B (Spec (.of R)) hR).map (toSpecOfAlgHomApp R B hR X A hA φ W x) =
      toSpecOfAlgHomChart R B hR X A φ W x :=
  B.inclusion.map_preimage _

/-- **The morphism `X ⟶ Spec A` over `Spec R` attached to an `R`-algebra homomorphism
`φ : A ⟶ Γ(X, 𝒪_X)`.**  On a scheme chart `x ∈ X(W)` it is the morphism `W ⟶ Spec A` of the
ring homomorphism `A ⟶ Γ(X, 𝒪_X) ⟶ Γ(W, 𝒪_W)`. -/
def toSpecOfAlgHom : X.obj ⟶ yoneda.obj (specSiteObject R B hR A hA) where
  app W := ↾fun x => toSpecOfAlgHomApp R B hR X A hA φ W.unop x
  naturality W W' g := by
    ext x
    apply Over.OverMorphism.ext
    apply B.inclusion.map_injective
    change B.inclusion.map (toSpecOfAlgHomApp R B hR X A hA φ W'.unop (X.obj.map g x)).left =
      B.inclusion.map (g.unop.left ≫ (toSpecOfAlgHomApp R B hR X A hA φ W.unop x).left)
    rw [B.inclusion.map_comp]
    change (BigFppfOver.toScheme B (Spec (.of R)) hR).map
        (toSpecOfAlgHomApp R B hR X A hA φ W'.unop (X.obj.map g x)) =
      (BigFppfOver.toScheme B (Spec (.of R)) hR).map g.unop ≫
        (BigFppfOver.toScheme B (Spec (.of R)) hR).map (toSpecOfAlgHomApp R B hR X A hA φ W.unop x)
    rw [toScheme_map_toSpecOfAlgHomApp, toScheme_map_toSpecOfAlgHomApp]
    exact (toSpecOfAlgHomChart_naturality R B hR X A φ g.unop x).symm

end Base

end AlgebraicGeometry.Space

end
