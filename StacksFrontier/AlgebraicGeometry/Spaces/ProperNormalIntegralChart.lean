module

public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageSectionsGlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.GlobalFunctionsColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleChartGlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureMapIsoCriteria

/-!
# The structure map of a proper morphism on a normal chart of the target

Let `f : X ⟶ Y` be a universally closed morphism of algebraic spaces and let `W` be an étale
chart of `Y` whose scheme is affine with an integrally closed domain `A = Γ(W, 𝒪_W)` of global
sections.  Suppose given a morphism `ι : K ⟶ W` of the site with `Γ(K, 𝒪_K)` a fraction field of
`A` through `ι` — in the application `K` is the spectrum of the function field of `W` — and a
cartesian-shaped square

```
X_K --τ--> X ×_Y W
 |hK          |
 v            v
 K  --ι-->    W
```

of algebraic spaces such that `Γ(K) ⟶ Γ(X_K)` is bijective and `Γ(X ×_Y W) ⟶ Γ(X_K)` is
injective.  Then the structure map `A ⟶ (f_* 𝒪_X)(W)` is bijective.

The sections of `f_* 𝒪_X` over `W` embed into `Γ(X ×_Y W)`
(`AlgebraicGeometry.Space.directImageSectionsToGlobalFunctions`), hence into
`Γ(X_K) = Γ(K)`, compatibly with `A`; they are integral over `A` (Stacks 0A0Q), and an integral
extension of an integrally closed domain embedded in its fraction field is trivial.  This is the
chartwise heart of Stacks 0AYI, in the form of the argument of Stacks 0AB1.

## Main results

* `AlgebraicGeometry.Space.bijective_algebraMap_pushforwardAlgebra_of_genericChart`: the
  statement above.

## References

* [Stacks Project, Tag 0AYI](https://stacks.math.columbia.edu/tag/0AYI)
* [Stacks Project, Tag 0AB1](https://stacks.math.columbia.edu/tag/0AB1)
* [Stacks Project, Tag 0A0Q](https://stacks.math.columbia.edu/tag/0A0Q)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The global function of the represented space of `V` attached to a regular function on `V`,
pulled back along the projection `X ×_Y V ⟶ V`, is the structure-algebra image of that regular
function under the bridge of `AlgebraicGeometry.Space.directImageSectionsToGlobalFunctions`. -/
theorem directImageSectionsToGlobalFunctions_algebraMap_eq_globalFunctionsMap
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    (r : Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj V), ⊤)) :
    directImageSectionsToGlobalFunctions B S hS f V
        ((pushforwardAlgebra B S hS (Over.mk f)).algebraMap (op V) r) =
      globalFunctionsMap B S hS (chartBaseChangeProjection B S hS f V)
        ((globalFunctionsYonedaRingEquiv B S hS
          ((SmallEtale.toOver B S hS Y.1).obj V)).symm r) := by
  apply Subtype.ext
  funext c
  induction c using Opposite.rec with | op c => ?_
  refine (directImageSectionsToGlobalFunctions_algebraMap B S hS f V c r).trans ?_
  have ht : yoneda.map
      (smallEtaleChartMapToBase B S hS (chartBaseChangeProjection B S hS f V).hom c) ≫
        (idEtaleChart B S hS ((SmallEtale.toOver B S hS Y.1).obj V)).obj.hom =
      c.obj.hom ≫ (chartBaseChangeProjection B S hS f V).hom :=
    (Category.comp_id _).trans (yoneda_map_smallEtaleChartMapToBase B S hS _ c)
  refine Eq.trans ?_ (globalFunctionsMap_val_of_chartHom B S hS
    (chartBaseChangeProjection B S hS f V)
    ((globalFunctionsYonedaRingEquiv B S hS ((SmallEtale.toOver B S hS Y.1).obj V)).symm r) c
    (idEtaleChart B S hS ((SmallEtale.toOver B S hS Y.1).obj V))
    (CostructuredArrow.homMk _ ht)).symm
  have hr := (globalFunctionsYonedaRingEquiv B S hS
    ((SmallEtale.toOver B S hS Y.1).obj V)).apply_symm_apply r
  rw [globalFunctionsYonedaRingEquiv_apply] at hr
  exact (congrArg (fun z => ((BigFppfOver.toScheme B S hS).map
    (smallEtaleChartMapToBase B S hS (chartBaseChangeProjection B S hS f V).hom c)).appTop.hom z)
    hr).symm

/-- Pullback of global functions along a morphism of represented spaces is, at the identity
charts, pullback of regular functions along the underlying morphism of schemes. -/
theorem globalFunctionsYonedaRingEquiv_globalFunctionsMap_schemeSpaceMap
    {U V : BigFppfOver B S hS} (g : U ⟶ V) (s : globalFunctions B S hS (yoneda.obj V)) :
    globalFunctionsYonedaRingEquiv B S hS U (globalFunctionsMap B S hS (schemeSpaceMap g) s) =
      ((BigFppfOver.toScheme B S hS).map g).appTop.hom
        (globalFunctionsYonedaRingEquiv B S hS V s) := by
  have ht : yoneda.map g ≫ (idEtaleChart B S hS V).obj.hom =
      (idEtaleChart B S hS U).obj.hom ≫ (schemeSpaceMap g).hom := by
    change yoneda.map g ≫ 𝟙 _ = 𝟙 _ ≫ yoneda.map g
    rw [Category.comp_id, Category.id_comp]
  exact globalFunctionsMap_val_of_chartHom B S hS (schemeSpaceMap g) s (idEtaleChart B S hS U)
    (idEtaleChart B S hS V) (CostructuredArrow.homMk g ht)

/-- **The structure map of a universally closed morphism is bijective on a normal chart carrying
a generic fibre with only constant global functions.**  See the module documentation. -/
theorem bijective_algebraMap_pushforwardAlgebra_of_genericChart {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (huc : UniversallyClosed B S hS f.hom) (W : SmallEtale B S hS Y.1)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj W))]
    [IsDomain Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj W), ⊤)]
    [IsIntegrallyClosed
      Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj W), ⊤)]
    {K : BigFppfOver B S hS} (ι : K ⟶ (SmallEtale.toOver B S hS Y.1).obj W)
    (hfrac : letI := ((BigFppfOver.toScheme B S hS).map ι).appTop.hom.toAlgebra
      IsFractionRing
        Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj W), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj K, ⊤))
    {XK : AlgebraicSpaces B S hS} (τ : XK ⟶ chartBaseChangeSpace B S hS f W)
    (hK : XK ⟶ schemeSpace K)
    (hsq : τ ≫ chartBaseChangeProjection B S hS f W = hK ≫ schemeSpaceMap ι)
    (hbij : Function.Bijective (globalFunctionsMap B S hS hK))
    (hinj : Function.Injective (globalFunctionsMap B S hS τ)) :
    Function.Bijective ((pushforwardAlgebra B S hS (Over.mk f)).algebraMap (op W)) := by
  let := ((BigFppfOver.toScheme B S hS).map ι).appTop.hom.toAlgebra
  have := hfrac
  let eW := globalFunctionsYonedaRingEquiv B S hS ((SmallEtale.toOver B S hS Y.1).obj W)
  let eK := globalFunctionsYonedaRingEquiv B S hS K
  let gK := RingEquiv.ofBijective (globalFunctionsMap B S hS hK) hbij
  let φ := eK.toRingHom.comp (gK.symm.toRingHom.comp ((globalFunctionsMap B S hS τ).comp
    (directImageSectionsToGlobalFunctions B S hS f W)))
  have hφ : Function.Injective φ :=
    eK.injective.comp (gK.symm.injective.comp
      (hinj.comp (injective_directImageSectionsToGlobalFunctions B S hS f W)))
  have hint : ((pushforwardAlgebra B S hS (Over.mk f)).algebraMap (op W)).IsIntegral :=
    isIntegral_pushforwardAlgebra_of_universallyClosed B S hS f huc W
      (inferInstanceAs (IsAffine
        ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj W))))
  refine Stacks.bijective_of_isIntegral_of_injective_comp_eq_algebraMap
    (A := Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj W), ⊤))
    (L := Γ((BigFppfOver.toScheme B S hS).obj K, ⊤)) _ hint φ hφ ?_
  ext r
  change eK (gK.symm (globalFunctionsMap B S hS τ (directImageSectionsToGlobalFunctions B S hS f W
    ((pushforwardAlgebra B S hS (Over.mk f)).algebraMap (op W) r)))) =
      ((BigFppfOver.toScheme B S hS).map ι).appTop.hom r
  rw [directImageSectionsToGlobalFunctions_algebraMap_eq_globalFunctionsMap]
  have h1 : globalFunctionsMap B S hS τ (globalFunctionsMap B S hS
      (chartBaseChangeProjection B S hS f W) (eW.symm r)) =
      globalFunctionsMap B S hS hK (globalFunctionsMap B S hS (schemeSpaceMap ι)
        (eW.symm r)) := by
    have hc1 := globalFunctionsMap_comp B S hS τ (chartBaseChangeProjection B S hS f W)
    have hc2 := globalFunctionsMap_comp B S hS hK (schemeSpaceMap ι)
    rw [hsq] at hc1
    exact (RingHom.congr_fun hc1.symm _).trans (RingHom.congr_fun hc2 _)
  have h2 : gK.symm (globalFunctionsMap B S hS hK
      (globalFunctionsMap B S hS (schemeSpaceMap ι) (eW.symm r))) =
      globalFunctionsMap B S hS (schemeSpaceMap ι) (eW.symm r) :=
    gK.symm_apply_apply _
  rw [h1, h2, globalFunctionsYonedaRingEquiv_globalFunctionsMap_schemeSpaceMap]
  exact congrArg _ (eW.apply_symm_apply r)

end AlgebraicGeometry.Space

end
