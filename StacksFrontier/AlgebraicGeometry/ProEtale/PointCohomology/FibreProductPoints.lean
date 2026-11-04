module

public import StacksFrontier.AlgebraicGeometry.Limits.Descending.InfiniteProducts
public import StacksFrontier.AlgebraicGeometry.ProEtale.PointCohomology.ContinuousSheaf
public import StacksFrontier.CategoryTheory.Sites.Continuous.CoveringPullbacks

/-!
# Geometric points of fibre products in the pro-étale site of a field

Let `U` be an object of the small pro-étale site of `Spec K` and let `Z = ∏ₐ Wₐ` be a finite
product, in the slice over `U`, of objects `Wₐ ⟶ U`. A geometric point of `Z` is the same as a
family of geometric points of the `Wₐ` with a common image in `U`: geometric points are
morphisms out of `Spec Kˢᵉᵖ`, which turn products into products. If `U` and the `Wₐ` are
affine then so is `Z`, the identification is a homeomorphism, and its compatibility with the
projections makes it natural with respect to the reindexing maps between such products.

## Main definitions

* `AlgebraicGeometry.GaloisSheaf.GeomPt.prodEquiv`: geometric points of a product as compatible
  families.

## Main results

* `AlgebraicGeometry.GaloisSheaf.isAffine_left_piObj`: finite fibre products of affine objects
  over an affine object are affine.
* `AlgebraicGeometry.GaloisSheaf.GeomPt.prodHomeomorph`: the identification is a homeomorphism
  over an affine base.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Topology

universe u w

namespace AlgebraicGeometry.GaloisSheaf

variable {K : Type u} [Field K]

/-- The underlying scheme of an object of the pro-étale site. -/
abbrev proEtToScheme (K : Type u) [Field K] : (base K).ProEt ⥤ Scheme.{u} :=
  Scheme.ProEt.forget (base K) ⋙ Over.forget (base K)

/-- **Finite fibre products of affine objects over an affine object are affine.** -/
theorem isAffine_left_piObj {U : (base K).ProEt} (hU : IsAffine U.left)
    (E : PreZeroHypercover.{w} U) (hX : ∀ i, IsAffine (E.X i).left) (p : ℕ)
    (i : Fin (p + 1) → E.I₀) [HasProduct fun a ↦ Over.mk (E.f (i a))] :
    IsAffine ((∏ᶜ (fun a ↦ Over.mk (E.f (i a)))).left).left := by
  let v : (base K).ProEt ⥤ Scheme.{u} := proEtToScheme K
  let A : Fin (p + 1) → Over U := fun a ↦ Over.mk (E.f (i a))
  have : IsAffine (v.obj U) := hU
  have : PreservesLimit (Discrete.functor A) (Over.post (X := U) v) :=
    Stacks.Sites.preservesLimit_fibreProducts_overPost v E
      (fun _ _ _ ↦ inferInstance) (fun _ _ _ ↦ inferInstance) p i
  have hF : ∀ a, IsAffineHom ((Over.post (X := U) v).obj (A a)).hom := fun a ↦
    have : IsAffine ((Over.post (X := U) v).obj (A a)).left := hX (i a)
    isAffineHom_of_isAffine _
  have : IsAffineHom (∏ᶜ (fun a ↦ (Over.post (X := U) v).obj (A a))).hom :=
    isAffineHom_over_finiteProduct _ hF
  have : IsAffine (∏ᶜ (fun a ↦ (Over.post (X := U) v).obj (A a))).left :=
    isAffine_of_isAffineHom (∏ᶜ (fun a ↦ (Over.post (X := U) v).obj (A a))).hom
  let e : ((∏ᶜ (fun a ↦ Over.mk (E.f (i a)))).left).left ≅
      (∏ᶜ (fun a ↦ (Over.post (X := U) v).obj (A a))).left :=
    (Over.forget (v.obj U)).mapIso (PreservesProduct.iso (Over.post (X := U) v) A)
  exact IsAffine.of_isIso e.hom

namespace GeomPt

/-- The morphism of the geometric point `map f ψ` is the morphism of `ψ` followed by `f`. -/
lemma toHom_map {V W : (base K).ProEt} (f : V ⟶ W) (ψ : GeomPt K V) :
    toHom (map f ψ) = toHom ψ ≫ f := rfl

variable {U : (base K).ProEt} {ι : Type*} {A : ι → (base K).ProEt} (f : ∀ a, A a ⟶ U)
  [HasProduct fun a ↦ Over.mk (f a)]

/-- Compatible families of geometric points of the members of a family over `U`. -/
abbrev Compatible : Type _ :=
  {ψ : ∀ a, GeomPt K (A a) // ∀ a b, map (f a) (ψ a) = map (f b) (ψ b)}

/-- The family of components of a geometric point of a product. -/
def prodComponents (θ : GeomPt K (∏ᶜ fun a ↦ Over.mk (f a)).left) : Compatible f :=
  ⟨fun a ↦ map (Pi.π (fun a ↦ Over.mk (f a)) a).left θ, fun a b ↦ by
    rw [← map_comp, ← map_comp]
    congr 1
    exact (Over.w (Pi.π (fun a ↦ Over.mk (f a)) a)).trans
      (Over.w (Pi.π (fun a ↦ Over.mk (f a)) b)).symm⟩

variable [Nonempty ι]

/-- The base point in `U` of a compatible family. -/
def basePoint (ψ : Compatible f) : GeomPt K U := map (f (Classical.arbitrary ι)) (ψ.1 _)

/-- The morphism into the product determined by a compatible family. -/
def prodPointHom (ψ : Compatible f) :
    Over.mk (toHom (basePoint f ψ)) ⟶ ∏ᶜ fun a ↦ Over.mk (f a) :=
  Pi.lift fun a ↦ Over.homMk (toHom (ψ.1 a)) (by
    change toHom (map (f a) (ψ.1 a)) = toHom (map (f _) (ψ.1 _))
    rw [ψ.2 a])

/-- Composing `prodPointHom f ψ` with the `a`-th projection gives the morphism of `ψ a`. -/
lemma prodPointHom_π (ψ : Compatible f) (a : ι) :
    (prodPointHom f ψ ≫ Pi.π (fun a ↦ Over.mk (f a)) a).left = toHom (ψ.1 a) := by
  rw [prodPointHom, Pi.lift_π]
  rfl

/-- The geometric point of a product with prescribed components. -/
def prodPoint (ψ : Compatible f) : GeomPt K (∏ᶜ fun a ↦ Over.mk (f a)).left :=
  map (prodPointHom f ψ).left unitPt

/-- The components of `prodPoint f ψ` are the family `ψ`. -/
lemma prodComponents_prodPoint (ψ : Compatible f) : prodComponents f (prodPoint f ψ) = ψ := by
  refine Subtype.ext (funext fun a ↦ ?_)
  change map (Pi.π (fun a ↦ Over.mk (f a)) a).left (map (prodPointHom f ψ).left unitPt) = _
  rw [← map_comp, ← Over.comp_left, prodPointHom_π]
  exact map_toHom_unitPt _

/-- A geometric point of the product is the point built from its components. -/
lemma prodPoint_prodComponents (θ : GeomPt K (∏ᶜ fun a ↦ Over.mk (f a)).left) :
    prodPoint f (prodComponents f θ) = θ := by
  have hθ : toHom θ ≫ (∏ᶜ fun a ↦ Over.mk (f a)).hom =
      toHom (basePoint f (prodComponents f θ)) := by
    change _ = toHom θ ≫ (Pi.π (fun a ↦ Over.mk (f a)) _).left ≫ f _
    rw [show (Pi.π (fun a ↦ Over.mk (f a)) (Classical.arbitrary ι)).left ≫
        f (Classical.arbitrary ι) = (∏ᶜ fun a ↦ Over.mk (f a)).hom from Over.w _]
  have hL : prodPointHom f (prodComponents f θ) = Over.homMk (toHom θ) hθ := by
    refine Pi.hom_ext _ _ fun a ↦ Over.OverMorphism.ext ?_
    rw [prodPointHom_π]
    rfl
  rw [prodPoint, hL]
  exact map_toHom_unitPt θ

/-- **Geometric points of a finite fibre product are compatible families of geometric points.** -/
def prodEquiv : GeomPt K (∏ᶜ fun a ↦ Over.mk (f a)).left ≃ Compatible f where
  toFun := prodComponents f
  invFun := prodPoint f
  left_inv := prodPoint_prodComponents f
  right_inv := prodComponents_prodPoint f

omit [Nonempty ι] in
/-- Taking the components of a geometric point of the product is continuous. -/
lemma continuous_prodComponents : Continuous (prodComponents f) :=
  Continuous.subtype_mk (continuous_pi fun _a ↦ continuous_map _) _

omit [Nonempty ι] in
/-- The components of the image of `θ` under the reindexing map `Pi.lift (fun b ↦ Pi.π _ (g b))`
are the components of `θ` at the indices `g b`. -/
lemma prodComponents_reindex {ι' : Type*} [Nonempty ι'] (g : ι' → ι)
    [HasProduct fun b ↦ Over.mk (f (g b))]
    (θ : GeomPt K (∏ᶜ fun a ↦ Over.mk (f a)).left) (b : ι') :
    (prodComponents (fun b ↦ f (g b)) (map (Pi.lift fun b ↦
      Pi.π (fun a ↦ Over.mk (f a)) (g b)).left θ)).1 b = (prodComponents f θ).1 (g b) := by
  change map _ (map _ θ) = map _ θ
  rw [← map_comp, ← Over.comp_left, Pi.lift_π]

/-- **Over an affine base, geometric points of a fibre product of affine objects are
compatible families, homeomorphically.** -/
def prodHomeomorph [IsAffine (∏ᶜ fun a ↦ Over.mk (f a)).left.left]
    [∀ a, IsAffine (A a).left] :
    GeomPt K (∏ᶜ fun a ↦ Over.mk (f a)).left ≃ₜ Compatible f :=
  (continuous_prodComponents f).homeoOfEquivCompactToT2 (f := prodEquiv f)

end GeomPt

end AlgebraicGeometry.GaloisSheaf
