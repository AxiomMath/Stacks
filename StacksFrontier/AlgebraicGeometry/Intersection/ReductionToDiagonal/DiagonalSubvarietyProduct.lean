module

public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProduct
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductAssociativity
public import StacksFrontier.AlgebraicGeometry.Chow.FieldSituation.Base
public import StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction.IntegralComponent
public import StacksFrontier.AlgebraicGeometry.F6Rank89.IdealSheafStalk
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SpecialFibreDimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.ImmersionsAndAffine.ProductSubscheme
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Product

/-!
# The diagonal and the product of two closed subvarieties

This file assembles the two closed subschemes of `X ×_k X` that the reduction to the diagonal
compares: the diagonal `Δ` itself, and the product `V ×_k W` of two closed subvarieties of `X`.

The diagonal is the reduced closure of the point `Δ(η)`, for `η` the generic point of an integral
`X`, so its ideal sheaf is the kernel of `Δ` and its local ideal at `Δ(z)` is the kernel of the
local ring map of `Δ` at `z`. The product `V ×_k W` is the closed subscheme cut out by
`pr₁^* I_V ⊔ pr₂^* I_W`; over an algebraically closed field it is again a variety, so it is the
reduced closure of its own generic point, that generic point projects to the generic points of
`V` and of `W`, and its dimension is `dim V + dim W`.

## Main definitions

* `Stacks.Intersection.ReductionToDiagonal.productIdealAt` — the ideal sheaf
  `pr₁^* I_V ⊔ pr₂^* I_W` of the product of the reduced closures of two points.
* `Stacks.Intersection.ReductionToDiagonal.productPointAt` — the generic point of that product.

## Main results

* `Stacks.Intersection.ReductionToDiagonal.integralComponentAt_image_genericPoint` — the reduced
  closure of the image of the generic point of an integral scheme under a quasi-compact morphism
  is the kernel of that morphism.
* `Stacks.Intersection.ReductionToDiagonal.localIdealAt_diagonal_eq_ker_stalkMap` — the local
  ideal of the diagonal at `Δ(z)` is the kernel of the local ring map of `Δ` at `z`.
* `Stacks.Intersection.ReductionToDiagonal.isIntegral_productIdealAt` — the product of two
  reduced point closures in a variety over an algebraically closed field is integral.
* `Stacks.Intersection.ReductionToDiagonal.fst_productPointAt` and `snd_productPointAt` — its
  generic point projects to the two points.
* `Stacks.Intersection.ReductionToDiagonal.integralComponentAt_productPointAt` — the product is
  the reduced closure of its generic point.
* `Stacks.Intersection.ReductionToDiagonal.topologicalKrullDim_productIdealAt` — its dimension is
  the sum of the two dimensions.
* `Stacks.Intersection.ReductionToDiagonal.exteriorProductWeight_productPointAt` and
  `Stacks.Intersection.ReductionToDiagonal.exteriorProductWeight_eq_zero_of_ne` — **the weight of
  a point in a product of two reduced point closures**: one at the generic point of the product,
  zero elsewhere.

## Implementation notes

The product is indexed by the two points rather than by two integral closed subschemes, as cycles
are; nothing is lost, since every integral closed subscheme is the reduced closure of its generic
point (`Stacks.Chow.integralComponentAt_genericPointOf`).

`Stacks.Chow.exteriorProductIdeal` is literally `productIdealAt`, the vanishing ideal of a point
closure being `Stacks.Chow.integralComponentAt` of that point; the two names are kept apart only
because the exterior product of cycles is set up for two different schemes over the base and this
file needs the square.

## References

* [Stacks Project, Lemma 43.19.2 (Tag 0B0U)](https://stacks.math.columbia.edu/tag/0B0U)
* [Stacks Project, Tag 05P3](https://stacks.math.columbia.edu/tag/05P3)
* [Stacks Project, Tag 0AZM](https://stacks.math.columbia.edu/tag/0AZM)
* [Stacks Project, Tag 02QU](https://stacks.math.columbia.edu/tag/02QU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Chow

universe u

namespace Stacks.Intersection.ReductionToDiagonal

/-! ### The ideal sheaf of the diagonal -/

/-- The kernel of a quasi-compact morphism with reduced source is a radical ideal sheaf. -/
theorem radical_ker_of_isReduced {X Z : Scheme.{u}} [IsReduced Z] (i : Z ⟶ X)
    [QuasiCompact i] : i.ker.radical = i.ker := by
  ext U : 2
  rw [Scheme.IdealSheafData.radical_ideal, Scheme.Hom.ker_apply]
  exact (Ideal.isRadical_bot.comap (i.app U).hom).radical

/-- **The reduced closure of the image of a generic point is the kernel.** For `i : Z ⟶ X` a
quasi-compact morphism with `Z` integral, the reduced induced structure on the closure of
`i(η)` is the closed subscheme cut out by the kernel of `i`. -/
theorem integralComponentAt_image_genericPoint {X Z : Scheme.{u}} [IsIntegral Z] (i : Z ⟶ X)
    [QuasiCompact i] : integralComponentAt (i.base (genericPoint Z)) = i.ker := by
  have h := (genericPoint_spec Z).image i.continuous
  have hc : Closeds.closure ({i.base (genericPoint Z)} : Set X) = i.ker.support := by
    apply SetLike.coe_injective
    simpa only [Set.image_univ, Closeds.coe_closure, Scheme.Hom.support_ker] using h.def
  rw [integralComponentAt, hc, Scheme.IdealSheafData.vanishingIdeal_support,
    radical_ker_of_isReduced]

/-- **The local ideal of the diagonal.** For `f : X ⟶ Y` a separated morphism with `X` integral,
the stalk at `Δ(z)` of the ideal sheaf of the diagonal — the reduced closure of `Δ(η)` — is the
kernel of the local ring map of `Δ` at `z`. -/
theorem localIdealAt_diagonal_eq_ker_stalkMap {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f]
    [IsIntegral X] (z : X) :
    AlgebraicGeometry.IdealSheafData.stalk
        (integralComponentAt ((pullback.diagonal f).base (genericPoint X)))
        ((pullback.diagonal f).base z) =
      RingHom.ker ((pullback.diagonal f).stalkMap z).hom := by
  have : IsClosedImmersion (pullback.diagonal f) := IsSeparated.isClosedImmersion_diagonal
  rw [integralComponentAt_image_genericPoint (pullback.diagonal f),
    AlgebraicGeometry.IdealSheafData.stalk_ker_of_isClosedImmersion (pullback.diagonal f) z]

/-! ### The product of two reduced point closures -/

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The ideal sheaf of the product of the reduced closures of two points of `X` inside
`X ×_k X`: the sum of the inverse images of their vanishing ideal sheaves. -/
abbrev productIdealAt (f : X ⟶ Spec (CommRingCat.of k)) (a b : X) :
    (pullback f f : Scheme.{u}).IdealSheafData :=
  (integralComponentAt a).comap (pullback.fst f f) ⊔
    (integralComponentAt b).comap (pullback.snd f f)

/-- The ideal sheaf of the product of two reduced point closures is the one the exterior product
of cycles is built from. -/
theorem exteriorProductIdeal_eq_productIdealAt (f : X ⟶ Spec (CommRingCat.of k)) (a b : X) :
    exteriorProductIdeal f f a b = productIdealAt f a b :=
  rfl

/-- The reduced closure of a point of a variety is itself a variety over the base field. -/
instance isVariety_subschemeι_integralComponentAt (f : X ⟶ Spec (CommRingCat.of k))
    [IsVariety k f] (a : X) : IsVariety k ((integralComponentAt a).subschemeι ≫ f) :=
  letI : IsIntegral (integralComponentAt a).subscheme := isIntegral_integralComponentAt a
  ⟨⟩

/-- The fibre product of the reduced closures of two points of a variety over an algebraically
closed field is a variety (Tag 05P3). -/
instance isVariety_pullback_integralComponentAt [IsAlgClosed k]
    (f : X ⟶ Spec (CommRingCat.of k)) [IsVariety k f] (a b : X) :
    IsVariety k (pullback.fst ((integralComponentAt a).subschemeι ≫ f)
      ((integralComponentAt b).subschemeι ≫ f) ≫ ((integralComponentAt a).subschemeι ≫ f)) :=
  isVariety_pullback k _ _

/-- **The product of two closed subvarieties of a variety over an algebraically closed field is
integral** (Tag 05P3): it is the fibre product of the two, which is again a variety. -/
instance isIntegral_productIdealAt [IsAlgClosed k] (f : X ⟶ Spec (CommRingCat.of k))
    [IsVariety k f] (a b : X) : IsIntegral (productIdealAt f a b).subscheme :=
  IsIntegral.of_isIso
    (Scheme.IdealSheafData.productSubschemeIso f f (integralComponentAt a)
      (integralComponentAt b)).symm.hom

/-- The generic point of the product of the reduced closures of two points, as a point of
`X ×_k X`. -/
def productPointAt [IsAlgClosed k] (f : X ⟶ Spec (CommRingCat.of k)) [IsVariety k f] (a b : X) :
    (pullback f f : Scheme.{u}) :=
  (productIdealAt f a b).subschemeι.base (genericPoint (productIdealAt f a b).subscheme)

/-- The generic point of the product is the generic point of the ideal sheaf cutting it out, in
the sense of `Stacks.Chow.genericPointOf`. -/
theorem productPointAt_eq_genericPointOf [IsAlgClosed k] (f : X ⟶ Spec (CommRingCat.of k))
    [IsVariety k f] (a b : X) :
    productPointAt f a b =
      genericPointOf (productIdealAt f a b) (isIntegral_productIdealAt f a b) :=
  rfl

/-- **The product of two reduced point closures is the reduced closure of its generic point.** -/
theorem integralComponentAt_productPointAt [IsAlgClosed k] (f : X ⟶ Spec (CommRingCat.of k))
    [IsVariety k f] (a b : X) :
    integralComponentAt (productPointAt f a b) = productIdealAt f a b :=
  integralComponentAt_genericPointOf _ (isIntegral_productIdealAt f a b)

/-- A flat morphism of integral schemes carries the generic point to the generic point: the
generic point of the target has a generalization in the source above it, and the only point
generalizing to the generic point of an integral scheme is that point. -/
theorem genericPoint_map_of_flat {A B : Scheme.{u}} [IsIntegral A] [IsIntegral B] (g : A ⟶ B)
    [Flat g] : g.base (genericPoint A) = genericPoint B := by
  have h : genericPoint B ⤳ g.base (genericPoint A) :=
    (genericPoint_spec B).specializes (Set.mem_univ _)
  obtain ⟨x, hx, hgx⟩ := Flat.generalizingMap g h
  have he : x = genericPoint A :=
    (hx.antisymm ((genericPoint_spec A).specializes (Set.mem_univ _))).eq
  simpa only [he] using hgx

/-- The generic point of the product of the reduced closures of `a` and `b` projects to `a`. -/
theorem fst_productPointAt [IsAlgClosed k] (f : X ⟶ Spec (CommRingCat.of k)) [IsVariety k f]
    (a b : X) : (pullback.fst f f).base (productPointAt f a b) = a := by
  have : IsIntegral (pullback ((integralComponentAt a).subschemeι ≫ f)
      ((integralComponentAt b).subschemeι ≫ f) : Scheme.{u}) := inferInstance
  have h := congrArg (fun q : (productIdealAt f a b).subscheme ⟶ X =>
      q.base (genericPoint (productIdealAt f a b).subscheme))
    (Scheme.IdealSheafData.productSubschemeIso_hom_fst_subschemeι f f (integralComponentAt a)
      (integralComponentAt b))
  simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h
  rw [genericPoint_map_of_flat
      (Scheme.IdealSheafData.productSubschemeIso f f (integralComponentAt a)
        (integralComponentAt b)).hom,
    genericPoint_map_of_flat (pullback.fst ((integralComponentAt a).subschemeι ≫ f)
      ((integralComponentAt b).subschemeι ≫ f))] at h
  have ha : (integralComponentAt a).subschemeι.base
      (genericPoint (integralComponentAt a).subscheme) = a :=
    genericPointOf_integralComponentAt a
  exact h.symm.trans ha

/-- The generic point of the product of the reduced closures of `a` and `b` projects to `b`. -/
theorem snd_productPointAt [IsAlgClosed k] (f : X ⟶ Spec (CommRingCat.of k)) [IsVariety k f]
    (a b : X) : (pullback.snd f f).base (productPointAt f a b) = b := by
  have : IsIntegral (pullback ((integralComponentAt a).subschemeι ≫ f)
      ((integralComponentAt b).subschemeι ≫ f) : Scheme.{u}) := inferInstance
  have h := congrArg (fun q : (productIdealAt f a b).subscheme ⟶ X =>
      q.base (genericPoint (productIdealAt f a b).subscheme))
    (Scheme.IdealSheafData.productSubschemeIso_hom_snd_subschemeι f f (integralComponentAt a)
      (integralComponentAt b))
  simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h
  rw [genericPoint_map_of_flat
      (Scheme.IdealSheafData.productSubschemeIso f f (integralComponentAt a)
        (integralComponentAt b)).hom,
    genericPoint_map_of_flat (pullback.snd ((integralComponentAt a).subschemeι ≫ f)
      ((integralComponentAt b).subschemeι ≫ f))] at h
  have hb : (integralComponentAt b).subschemeι.base
      (genericPoint (integralComponentAt b).subscheme) = b :=
    genericPointOf_integralComponentAt b
  exact h.symm.trans hb

/-! ### The dimension of the product -/

/-- **The product of two reduced point closures has the sum of the two dimensions** (Tag 0AZM):
it is the fibre product of the two closures, both varieties over the base field. -/
theorem topologicalKrullDim_productIdealAt [IsAlgClosed k] (f : X ⟶ Spec (CommRingCat.of k))
    [IsVariety k f] (a b : X) :
    topologicalKrullDim (productIdealAt f a b).subscheme =
      topologicalKrullDim (integralComponentAt a).subscheme +
        topologicalKrullDim (integralComponentAt b).subscheme := by
  rw [IsHomeomorph.topologicalKrullDim_eq _
      (Scheme.Hom.homeomorph (Scheme.IdealSheafData.productSubschemeIso f f
        (integralComponentAt a) (integralComponentAt b)).hom).isHomeomorph,
    topologicalKrullDim_pullback_of_isVariety k ((integralComponentAt a).subschemeι ≫ f)
      ((integralComponentAt b).subschemeι ≫ f)]

/-- **The relative dimension of the generic point of a product of two reduced point closures** is
the sum of the relative dimensions of the two points. -/
theorem relativeDimension_productPointAt [IsAlgClosed k] (f : X ⟶ Spec (CommRingCat.of k))
    [IsVariety k f] (a b : X) :
    relativeDimension (fieldChowSituation k).dimensionFunction (pullback.fst f f ≫ f)
        (productPointAt f a b) =
      relativeDimension (fieldChowSituation k).dimensionFunction f a +
        relativeDimension (fieldChowSituation k).dimensionFunction f b := by
  have hva : topologicalKrullDim ((integralComponentAt a).support : Set X) =
      (relativeDimension (fieldChowSituation k).dimensionFunction f a).toNat := by
    rw [show ((integralComponentAt a).support : Set X) = closure ({a} : Set X) from
      coe_support_integralComponentAt a, topologicalKrullDim_closure_singleton_eq k f a]
  have hvb : topologicalKrullDim ((integralComponentAt b).support : Set X) =
      (relativeDimension (fieldChowSituation k).dimensionFunction f b).toNat := by
    rw [show ((integralComponentAt b).support : Set X) = closure ({b} : Set X) from
      coe_support_integralComponentAt b, topologicalKrullDim_closure_singleton_eq k f b]
  have hvv : topologicalKrullDim ((productIdealAt f a b).support :
        Set (pullback f f : Scheme.{u})) =
      (relativeDimension (fieldChowSituation k).dimensionFunction (pullback.fst f f ≫ f)
        (productPointAt f a b)).toNat := by
    rw [show ((productIdealAt f a b).support : Set (pullback f f : Scheme.{u})) =
          closure ({productPointAt f a b} : Set (pullback f f : Scheme.{u})) from
        support_eq_closure_genericPointOf _ (isIntegral_productIdealAt f a b),
      topologicalKrullDim_closure_singleton_eq k (pullback.fst f f ≫ f) (productPointAt f a b)]
  have hkey := topologicalKrullDim_productIdealAt f a b
  rw [Stacks.Chow.topologicalKrullDim_subscheme, Stacks.Chow.topologicalKrullDim_subscheme,
    Stacks.Chow.topologicalKrullDim_subscheme, hva, hvb, hvv] at hkey
  have hnat : (relativeDimension (fieldChowSituation k).dimensionFunction (pullback.fst f f ≫ f)
        (productPointAt f a b)).toNat =
      (relativeDimension (fieldChowSituation k).dimensionFunction f a).toNat +
        (relativeDimension (fieldChowSituation k).dimensionFunction f b).toNat := by
    exact_mod_cast hkey
  have ha := relativeDimension_fieldChowSituation_nonneg k f a
  have hb := relativeDimension_fieldChowSituation_nonneg k f b
  have hv := relativeDimension_fieldChowSituation_nonneg k (pullback.fst f f ≫ f)
    (productPointAt f a b)
  omega

/-- The delta-dimension of the product of two reduced point closures is the sum of the two
relative dimensions. -/
theorem schemeDeltaDimension_productIdealAt [IsAlgClosed k] (f : X ⟶ Spec (CommRingCat.of k))
    [IsVariety k f] (a b : X) :
    schemeDeltaDimension (fieldChowSituation k)
        ((productIdealAt f a b).subschemeι ≫ (pullback.fst f f ≫ f)) =
      ((relativeDimension (fieldChowSituation k).dimensionFunction f a +
        relativeDimension (fieldChowSituation k).dimensionFunction f b : ℤ) : EInt) := by
  rw [schemeDeltaDimension_eq_genericPoint (fieldChowSituation k)
      ((productIdealAt f a b).subschemeι ≫ (pullback.fst f f ≫ f)),
    relativeDimension_comp_closedImmersion]
  exact congrArg (fun m : ℤ => (m : EInt)) (relativeDimension_productPointAt f a b)

/-! ### The weight of a point in a product of two reduced point closures -/

/-- The weight of a point in a product of two reduced point closures, in the expected dimension,
is the coefficient at that point of the fundamental cycle of the product. -/
theorem exteriorProductWeight_eq_cycleAssociatedToClosedSubscheme
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f] (a b : X)
    (z : (pullback f f : Scheme.{u})) (j : ℤ) :
    exteriorProductWeight (fieldChowSituation k) f f j a b z =
      (cycleAssociatedToClosedSubscheme (fieldChowSituation k) (pullback.fst f f ≫ f)
        (productIdealAt f a b).subschemeι j).1 z :=
  rfl

/-- **The weight of the generic point of the product of two reduced point closures is one.**
Over an algebraically closed field the product of two closed subvarieties is again a
subvariety, so its fundamental cycle in the expected dimension is the prime cycle of its generic
point with coefficient one (Tag 02QU). -/
theorem exteriorProductWeight_productPointAt [IsAlgClosed k]
    (f : X ⟶ Spec (CommRingCat.of k)) [IsVariety k f] (a b : X) :
    exteriorProductWeight (fieldChowSituation k) f f
        (relativeDimension (fieldChowSituation k).dimensionFunction f a +
          relativeDimension (fieldChowSituation k).dimensionFunction f b) a b
        (productPointAt f a b) = 1 := by
  rw [exteriorProductWeight_eq_cycleAssociatedToClosedSubscheme, productPointAt_eq_genericPointOf]
  exact cycleAssociatedToClosedSubscheme_integral_apply (fieldChowSituation k)
    (pullback.fst f f ≫ f) (productIdealAt f a b) (isIntegral_productIdealAt f a b)
    (schemeDeltaDimension_productIdealAt f a b)

/-- **Away from its generic point the product of two reduced point closures has no weight.** -/
theorem exteriorProductWeight_eq_zero_of_ne [IsAlgClosed k]
    (f : X ⟶ Spec (CommRingCat.of k)) [IsVariety k f] (a b : X) (j : ℤ)
    {z : (pullback f f : Scheme.{u})} (hz : z ≠ productPointAt f a b) :
    exteriorProductWeight (fieldChowSituation k) f f j a b z = 0 := by
  rw [exteriorProductWeight_eq_cycleAssociatedToClosedSubscheme]
  exact cycleAssociatedToClosedSubscheme_integral_apply_of_ne (fieldChowSituation k)
    (pullback.fst f f ≫ f) (productIdealAt f a b) (isIntegral_productIdealAt f a b) j hz

end Stacks.Intersection.ReductionToDiagonal

end
