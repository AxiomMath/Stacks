module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveLiftsGlue
public import StacksFrontier.Deformation.Artin.Infinitesimal.FunctorDataComparison

/-!
# The tangent functor and the infinitesimal automorphisms of a curve over a field

Let `x = (X → Spec k)` be a family of curves over a field `k`, an object of `Curvesstack` over
`Spec k`. We show that the tangent functor `T_x` and the functor of infinitesimal automorphisms
`Inf_x` of Stacks 07Y9 exist for `x`, and that `T_x(k)` and `Inf_x(k)` are finite-dimensional
`k`-vector spaces. This is part (2) of Stacks 0D57.

The construction of Stacks 07Y9 uses the condition (RS*) only through the two product
conditions: restriction from `k[M × N]` to `k[M]` and `k[N]` is a bijection on isomorphism
classes of lifts of `x`, and on infinitesimal automorphisms of the trivial lift. Both are proved
here for families of curves (`CurveLift.liftClasses_product_bijective`,
`CurveLift.infinitesimalAutomorphismSetFunctor_product_bijective`) by gluing along the pushout
`Spec k[M × N] = Spec k[M] ⨿_{Spec k} Spec k[N]` (Stacks 07RV, 07RX). Finite-dimensionality is
then transported from the deformation category `𝓕_{𝒳,k,x}`, whose tangent space and
infinitesimal automorphisms are finite-dimensional by part (1)
(`CurveDeformation.finiteDimensional_predeformation`), through the comparison of Stacks 0D18.

## Main results

* `AlgebraicGeometry.finiteDimensional_curves_tangentFunctor_infinitesimalAutomorphismFunctor`
  — **Stacks 0D57 (2)**.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Deformation Deformation.Artin

namespace AlgebraicGeometry

universe u

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- A family of curves over `Spec k`, read in the slice over `Spec ℤ`, lies over `Spec k` with
the structure map of the trivial `k`-algebra `k`. -/
theorem projection_obj_eq_of_curvesProjectionOver_obj_eq {k : Type u} [Field k]
    {toS : Spec (.of k) ⟶ integerBase} {hk : B.Contains (Spec (.of k))} (x : CurveFamily B hZ)
    (hx : (curvesProjectionOver B hZ).obj x = algebraOver k B integerBase hZ toS hk) :
    (CurveDeformation.projection B hZ).obj x =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k k)) ≫ toS) := by
  show (Over.post B.inclusion).obj ((curvesProjectionOver B hZ).obj x) = _
  rw [hx]
  have h : Spec.map (CommRingCat.ofHom (algebraMap k k)) ≫ toS = toS := by
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
  rw [h]
  rfl

/-- Let `k` be a field and let `x = (X → Spec k)` be a family of curves over `Spec k`. Then the
tangent functor `T_x` and the functor of infinitesimal automorphisms `Inf_x` of Stacks 07Y9 exist,
and `T_x(k)` and `Inf_x(k)` are finite-dimensional `k`-vector spaces.

Each functor is stated as a structure (`TangentFunctorData`,
`InfinitesimalAutomorphismFunctorData`) carrying a `k`-linear functor on the site modules together
with its identification with the isomorphism classes of lifts of `x`, respectively with the
infinitesimal automorphisms of the trivial lifts of `x`, natural in the module. The statement
gives that such a functor exists and that the value at `k` of *every* such functor is
finite-dimensional, so it holds for the functors `T_x` and `Inf_x` of Stacks 07Y9, which are
determined by these identifications. No condition on `k` is assumed. -/
@[stacks 0D57 "(2): for a family of curves x over a field k, the tangent functor T_x and the \
functor Inf_x of Stacks 07Y9 exist, and T_x(k) and Inf_x(k) are finite dimensional; both \
are stated for every k-linear functor carrying the identifications of 07Y9"]
theorem finiteDimensional_curves_tangentFunctor_infinitesimalAutomorphismFunctor {k : Type u}
    [Field k] {toS : Spec (.of k) ⟶ integerBase} {hk : B.Contains (Spec (.of k))}
    (x : CurveFamily B hZ)
    (hx : (curvesProjectionOver B hZ).obj x = algebraOver k B integerBase hZ toS hk) :
    (Nonempty (TangentFunctorData k B integerBase hZ toS hk (curvesProjectionOver B hZ) x hx) ∧
      ∀ T : TangentFunctorData k B integerBase hZ toS hk (curvesProjectionOver B hZ) x hx,
        FiniteDimensional k (T.functor.obj ((fgSiteModule B hk).obj (FGModuleCat.of k k)))) ∧
    (Nonempty (InfinitesimalAutomorphismFunctorData k B integerBase hZ toS hk
        (curvesProjectionOver B hZ) x hx
        CurveDeformation.curvesProjectionOver_isFiberedInGroupoids) ∧
      ∀ I : InfinitesimalAutomorphismFunctorData k B integerBase hZ toS hk
          (curvesProjectionOver B hZ) x hx
          CurveDeformation.curvesProjectionOver_isFiberedInGroupoids,
        FiniteDimensional k (I.functor.obj ((fgSiteModule B hk).obj (FGModuleCat.of k k)))) := by
  have hp := CurveDeformation.curvesProjectionOver_isFiberedInGroupoids (B := B) (hZ := hZ)
  have hx₀ := projection_obj_eq_of_curvesProjectionOver_obj_eq x hx
  obtain ⟨hD, hT, hI⟩ := CurveDeformation.finiteDimensional_predeformation (iΛ := toS) x hx₀
  refine ⟨⟨nonempty_tangentFunctorData_of_bijective k B integerBase hZ toS hk
      (curvesProjectionOver B hZ) x hx hp
      (fun M N => CurveLift.liftClasses_product_bijective x hx hp M N), fun T => ?_⟩,
    ⟨nonempty_infinitesimalAutomorphismFunctorData_of_bijective k B integerBase hZ toS hk
      (curvesProjectionOver B hZ) x hx hp
      (fun M N => CurveLift.infinitesimalAutomorphismSetFunctor_product_bijective x hx
        (M := M) (N := N) hp), fun I => ?_⟩⟩
  · exact finiteDimensional_tangentFunctorData_of_artinianTangentSpace B integerBase hZ toS toS hk
      (curvesProjectionOver B hZ) hp x hx₀ hx T hD hT
  · exact finiteDimensional_infinitesimalAutomorphismFunctorData B integerBase hZ toS toS hk
      (curvesProjectionOver B hZ) hp x hx₀ hx I hD hI

end AlgebraicGeometry
