module

public import StacksFrontier.Deformation.Applications.TwoFibreProductInfRow
public import StacksFrontier.Deformation.Cofibered.Product

/-!
# The infinitesimal automorphisms and the tangent space of a product of deformation categories

Let `𝓕` and `𝓖` be deformation categories over `𝒞_Λ` and let `𝓕 × 𝓖` be their product, which
item (14) of Remarks 90.5.2 (Tag 0DZJ) defines to be the `2`-fibre product `𝓕 ×_{𝒞_Λ} 𝓖` over
the base category, `Deformation.cofiberedProduct`. This file proves that `𝓕 × 𝓖` is again a
deformation category, and that its two invariants are the products of those of the factors:

`Inf(𝓕 × 𝓖) ≅ Inf(𝓕) × Inf(𝓖)` and `T(𝓕 × 𝓖) ≅ T𝓕 × T𝓖`

as `k`-vector spaces, the isomorphisms being the pairs of the maps induced by the two
projections. This is what lets a statement whose terms are `Inf(𝓕 × 𝓖)` and `T(𝓕 × 𝓖)` be
read on the products of the invariants of the factors: for a morphism `𝓗 → 𝓕 × 𝓖` given by a
pair `(φ, ψ)`, the pair of the maps induced by `φ` and `ψ` is the map induced by `𝓗 → 𝓕 × 𝓖`
followed by these isomorphisms.

## Main definitions

* `Deformation.cofiberedProductFiberHom`, `Deformation.cofiberedProductFiberIso`: an arrow
  (an isomorphism) of a fibre of `𝓕 × 𝓖` from a pair of arrows (isomorphisms) of the fibres of
  `𝓕` and `𝓖` between the components.
* `Deformation.cofiberedProductTangentPair`, `Deformation.cofiberedProductTangentEquiv`: the
  pair of the maps induced on tangent modules by the two projections, and the `k`-linear
  equivalence `T(𝓕 × 𝓖)(M) ≃ₗ[k] T𝓕(M) × T𝓖(M)` it is, at every coordinate module `M`.
* `Deformation.cofiberedProductInfPair`, `Deformation.cofiberedProductInfEquiv`: the pair of the
  maps induced on infinitesimal automorphisms by the two projections, and the `k`-linear
  equivalence `Inf(𝓕 × 𝓖) ≃ₗ[k] Inf(𝓕) × Inf(𝓖)` it is, at every base point.

## Main results

* `Deformation.bijective_cofiberedProductTangentPair`,
  `Deformation.bijective_cofiberedProductInfPair`: the two pairs are bijective.
* `Deformation.prod_tangentMapAt_eq_cofiberedProductTangentEquiv_comp`,
  `Deformation.prod_inducedInfinitesimalLinearMapOfEq_apply_eq_cofiberedProductInfEquiv`: for
  morphisms `φ : 𝓗 → 𝓕` and `ψ : 𝓗 → 𝓖` over `𝒞_Λ`, the pair of the maps they induce is the map
  induced by `Deformation.cofiberedProductLift φ ψ : 𝓗 → 𝓕 × 𝓖` followed by the equivalence.

## Implementation notes

The source of Tag 0E3V reads both identifications off as evident, and they are: over the base
category itself a vertical arrow of the identity functor is forced to be the canonical
identification (`Deformation.cofiberedProduct_iso_hom`), so an object of `𝓕 × 𝓖` over `U` is
a pair of objects over `U` and an arrow of it over `U ⟶ U'` is a pair of arrows over
`U ⟶ U'`, the comparison square commuting automatically (`Deformation.cofiberedProduct_w`).
On tangent spaces this makes the pair of projections bijective on isomorphism classes over
`k[M]` directly. On infinitesimal automorphisms the map induced by a projection is conjugation
by the comparison of chosen pushforwards
(`Deformation.inducedInfinitesimalLinearMapOfEq_spec_iso`), so a pair of infinitesimal
automorphisms of the two components is, after conjugation, a pair of automorphisms of the
components of the chosen pushforward of the base point, hence an automorphism of it; it is
infinitesimal because the special fibre of the predeformation category `𝓕 × 𝓖` is thin
(`Deformation.ker_transportAutHom_eq_top_of_isThin`).

The six-term sequence of Tag 06L5 for `𝓕 ×_{𝒞_Λ} 𝓖`, with `Inf(𝒞_Λ) = T𝒞_Λ = 0`, gives the same
bijectivity, but its spot at `Inf(𝓕) ⊕ Inf(𝓖)` is stated for a base point lying over the
residue-field object `Deformation.residueFieldObject` itself; the direct argument here needs no
condition on the base point, which is what a base point over an isomorphic copy of the residue
field requires.

## References

* [Stacks Project, Tag 0DZJ](https://stacks.math.columbia.edu/tag/0DZJ)
* [Stacks Project, Tag 06L5](https://stacks.math.columbia.edu/tag/06L5)
* [Stacks Project, Tag 0E3V](https://stacks.math.columbia.edu/tag/0E3V)
-/

@[expose] public noncomputable section

namespace Deformation

open CategoryTheory

universe u w u₁ v₁ u₂ v₂ u₃ v₃

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {𝓕 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, w, w} Λ k)}
  {𝓖 : BasedCategory.{v₂, u₂} (ArtinianLocalAlgCat.{u, w, w} Λ k)}
  {𝓗 : BasedCategory.{v₃, u₃} (ArtinianLocalAlgCat.{u, w, w} Λ k)}

/-! ### Arrows of a fibre of the product from pairs of arrows -/

section Fiber

variable {A : ArtinianLocalAlgCat.{u, w, w} Λ k}

/-- An arrow of the fibre of `𝓕 × 𝓖` over `A` from a pair of arrows of the fibres of `𝓕` and of
`𝓖` over `A` between the two components. No compatibility is needed, the comparison square of
the product commuting automatically. -/
def cofiberedProductFiberHom (W₁ W₂ : (cofiberedProduct 𝓕 𝓖).p.Fiber A)
    (a : (fiberFunctor (cofiberedProductFst 𝓕 𝓖) A).obj W₁ ⟶
      (fiberFunctor (cofiberedProductFst 𝓕 𝓖) A).obj W₂)
    (b : (fiberFunctor (cofiberedProductSnd 𝓕 𝓖) A).obj W₁ ⟶
      (fiberFunctor (cofiberedProductSnd 𝓕 𝓖) A).obj W₂) : W₁ ⟶ W₂ :=
  ⟨cofiberedProductHom (P := W₁.1) (Q := W₂.1) (eqToHom W₁.2 ≫ 𝟙 A ≫ eqToHom W₂.2.symm) a.1 b.1
      (by
        have h : 𝓕.p.IsHomLift (𝟙 A) a.1 := a.2
        exact (inferInstance :
          𝓕.p.IsHomLift (eqToHom W₁.2 ≫ 𝟙 A ≫ eqToHom W₂.2.symm) a.1))
      (by
        have h : 𝓖.p.IsHomLift (𝟙 A) b.1 := b.2
        exact (inferInstance :
          𝓖.p.IsHomLift (eqToHom W₁.2 ≫ 𝟙 A ≫ eqToHom W₂.2.symm) b.1)),
    IsHomLift.of_fac' _ (𝟙 A) _ W₁.2 W₂.2 rfl⟩

/-- The `𝓕`-component of `cofiberedProductFiberHom W₁ W₂ a b` is `a`. -/
@[simp]
theorem cofiberedProductFiberHom_val_a (W₁ W₂ : (cofiberedProduct 𝓕 𝓖).p.Fiber A)
    (a : (fiberFunctor (cofiberedProductFst 𝓕 𝓖) A).obj W₁ ⟶
      (fiberFunctor (cofiberedProductFst 𝓕 𝓖) A).obj W₂)
    (b : (fiberFunctor (cofiberedProductSnd 𝓕 𝓖) A).obj W₁ ⟶
      (fiberFunctor (cofiberedProductSnd 𝓕 𝓖) A).obj W₂) :
    (cofiberedProductFiberHom W₁ W₂ a b).1.a = a.1 := rfl

/-- The `𝓖`-component of `cofiberedProductFiberHom W₁ W₂ a b` is `b`. -/
@[simp]
theorem cofiberedProductFiberHom_val_b (W₁ W₂ : (cofiberedProduct 𝓕 𝓖).p.Fiber A)
    (a : (fiberFunctor (cofiberedProductFst 𝓕 𝓖) A).obj W₁ ⟶
      (fiberFunctor (cofiberedProductFst 𝓕 𝓖) A).obj W₂)
    (b : (fiberFunctor (cofiberedProductSnd 𝓕 𝓖) A).obj W₁ ⟶
      (fiberFunctor (cofiberedProductSnd 𝓕 𝓖) A).obj W₂) :
    (cofiberedProductFiberHom W₁ W₂ a b).1.b = b.1 := rfl

/-- An isomorphism of the fibre of `𝓕 × 𝓖` over `A` from a pair of isomorphisms of the fibres of
`𝓕` and of `𝓖` over `A` between the two components. -/
def cofiberedProductFiberIso (W₁ W₂ : (cofiberedProduct 𝓕 𝓖).p.Fiber A)
    (a : (fiberFunctor (cofiberedProductFst 𝓕 𝓖) A).obj W₁ ≅
      (fiberFunctor (cofiberedProductFst 𝓕 𝓖) A).obj W₂)
    (b : (fiberFunctor (cofiberedProductSnd 𝓕 𝓖) A).obj W₁ ≅
      (fiberFunctor (cofiberedProductSnd 𝓕 𝓖) A).obj W₂) : W₁ ≅ W₂ where
  hom := cofiberedProductFiberHom W₁ W₂ a.hom b.hom
  inv := cofiberedProductFiberHom W₂ W₁ a.inv b.inv
  hom_inv_id := Functor.Fiber.hom_ext (TwoFibreProductOver.Hom.ext'
    (by exact congrArg Subtype.val a.hom_inv_id) (by exact congrArg Subtype.val b.hom_inv_id))
  inv_hom_id := Functor.Fiber.hom_ext (TwoFibreProductOver.Hom.ext'
    (by exact congrArg Subtype.val a.inv_hom_id) (by exact congrArg Subtype.val b.inv_hom_id))

end Fiber

/-! ### The tangent space of the product -/

section Tangent

variable (h𝓕 : IsDeformationCategory.{u, w, w} 𝓕.p) (h𝓖 : IsDeformationCategory.{u, w, w} 𝓖.p)

/-- The map `T(𝓕 × 𝓖) → T𝓕 × T𝓖` at a coordinate module `M`: the pair of the `k`-linear maps
induced on tangent modules by the two projections of the product. -/
def cofiberedProductTangentPair (M : FGModuleCat.{w} k) :
    ↥(tangentModuleAt.{u, w, w} (cofiberedProduct 𝓕 𝓖)
        (isDeformationCategory_cofiberedProduct_of_isDeformationCategory_id h𝓕 h𝓖) M) →ₗ[k]
      ↥(tangentModuleAt.{u, w, w} 𝓕 h𝓕 M) × ↥(tangentModuleAt.{u, w, w} 𝓖 h𝓖 M) :=
  LinearMap.prod
    (tangentMapAt.{u, w, w}
        (isDeformationCategory_cofiberedProduct_of_isDeformationCategory_id h𝓕 h𝓖) h𝓕
      (cofiberedProductFst 𝓕 𝓖) M)
    (tangentMapAt.{u, w, w}
        (isDeformationCategory_cofiberedProduct_of_isDeformationCategory_id h𝓕 h𝓖) h𝓖
      (cofiberedProductSnd 𝓕 𝓖) M)

/-- `cofiberedProductTangentPair` sends a tangent vector `t` of `𝓕 × 𝓖` to the pair of its
images under the maps induced by the two projections. -/
theorem cofiberedProductTangentPair_apply (M : FGModuleCat.{w} k)
    (t : ↥(tangentModuleAt.{u, w, w} (cofiberedProduct 𝓕 𝓖)
      (isDeformationCategory_cofiberedProduct_of_isDeformationCategory_id h𝓕 h𝓖) M)) :
    cofiberedProductTangentPair h𝓕 h𝓖 M t =
      (tangentMapAt.{u, w, w}
          (isDeformationCategory_cofiberedProduct_of_isDeformationCategory_id h𝓕 h𝓖) h𝓕
          (cofiberedProductFst 𝓕 𝓖) M t,
        tangentMapAt.{u, w, w}
            (isDeformationCategory_cofiberedProduct_of_isDeformationCategory_id h𝓕 h𝓖) h𝓖
          (cofiberedProductSnd 𝓕 𝓖) M t) :=
  rfl

/-- **The tangent space of a product is the product of the tangent spaces.** The pair of the maps
induced on tangent modules by the two projections `𝓕 × 𝓖 → 𝓕` and `𝓕 × 𝓖 → 𝓖` is bijective, at
every coordinate module `M`: two objects of `𝓕 × 𝓖` over `k[M]` are isomorphic exactly when
their components are, and every pair of objects of `𝓕` and `𝓖` over `k[M]` is an object of
`𝓕 × 𝓖` over `k[M]`. -/
theorem bijective_cofiberedProductTangentPair (M : FGModuleCat.{w} k) :
    Function.Bijective (cofiberedProductTangentPair h𝓕 h𝓖 M) := by
  refine ⟨fun s t hst => ?_, fun st => ?_⟩
  · obtain ⟨W₁, rfl⟩ := tangentClassAt_surjective.{u, w, w} (cofiberedProduct 𝓕 𝓖)
      (isDeformationCategory_cofiberedProduct_of_isDeformationCategory_id h𝓕 h𝓖) M s
    obtain ⟨W₂, rfl⟩ := tangentClassAt_surjective.{u, w, w} (cofiberedProduct 𝓕 𝓖)
      (isDeformationCategory_cofiberedProduct_of_isDeformationCategory_id h𝓕 h𝓖) M t
    have h1 := congrArg Prod.fst hst
    have h2 := congrArg Prod.snd hst
    simp only [cofiberedProductTangentPair_apply, tangentMapAt_tangentClassAt,
      tangentClassAt_eq_iff] at h1 h2
    obtain ⟨a⟩ := h1
    obtain ⟨b⟩ := h2
    exact (tangentClassAt_eq_iff.{u, w, w} (cofiberedProduct 𝓕 𝓖)
      (isDeformationCategory_cofiberedProduct_of_isDeformationCategory_id h𝓕 h𝓖) M W₁ W₂).2
      ⟨cofiberedProductFiberIso W₁ W₂ a b⟩
  · obtain ⟨s, t⟩ := st
    obtain ⟨x, rfl⟩ := tangentClassAt_surjective.{u, w, w} 𝓕 h𝓕 M s
    obtain ⟨y, rfl⟩ := tangentClassAt_surjective.{u, w, w} 𝓖 h𝓖 M t
    refine ⟨tangentClassAt.{u, w, w} (cofiberedProduct 𝓕 𝓖)
      (isDeformationCategory_cofiberedProduct_of_isDeformationCategory_id h𝓕 h𝓖) M
      ⟨cofiberedProductObj _ x.1 y.1 x.2 y.2, rfl⟩, ?_⟩
    refine Prod.ext ?_ ?_
    · exact tangentMapAt_tangentClassAt.{u, w, w}
        (isDeformationCategory_cofiberedProduct_of_isDeformationCategory_id h𝓕 h𝓖)
        h𝓕 (cofiberedProductFst 𝓕 𝓖) M _
    · exact tangentMapAt_tangentClassAt.{u, w, w}
        (isDeformationCategory_cofiberedProduct_of_isDeformationCategory_id h𝓕 h𝓖)
        h𝓖 (cofiberedProductSnd 𝓕 𝓖) M _

/-- **`T(𝓕 × 𝓖) ≅ T𝓕 × T𝓖`**: the tangent module of the product of two deformation categories at a
coordinate module `M` is `k`-linearly the product of their tangent modules, by the pair of the
maps induced by the two projections. At the rank-one module this identifies the tangent space
`T(𝓕 × 𝓖)` of Tag 06I9, with its vector-space structure of Tag 06IH, with `T𝓕 × T𝓖`. -/
def cofiberedProductTangentEquiv (M : FGModuleCat.{w} k) :
    ↥(tangentModuleAt.{u, w, w} (cofiberedProduct 𝓕 𝓖)
        (isDeformationCategory_cofiberedProduct_of_isDeformationCategory_id h𝓕 h𝓖) M) ≃ₗ[k]
      ↥(tangentModuleAt.{u, w, w} 𝓕 h𝓕 M) × ↥(tangentModuleAt.{u, w, w} 𝓖 h𝓖 M) :=
  LinearEquiv.ofBijective (cofiberedProductTangentPair h𝓕 h𝓖 M)
    (bijective_cofiberedProductTangentPair h𝓕 h𝓖 M)

/-- The equivalence `cofiberedProductTangentEquiv` agrees pointwise with
`cofiberedProductTangentPair`. -/
@[simp]
theorem cofiberedProductTangentEquiv_apply (M : FGModuleCat.{w} k)
    (t : ↥(tangentModuleAt.{u, w, w} (cofiberedProduct 𝓕 𝓖)
      (isDeformationCategory_cofiberedProduct_of_isDeformationCategory_id h𝓕 h𝓖) M)) :
    cofiberedProductTangentEquiv h𝓕 h𝓖 M t = cofiberedProductTangentPair h𝓕 h𝓖 M t :=
  rfl

/-- The underlying linear map of `cofiberedProductTangentEquiv` is
`cofiberedProductTangentPair`. -/
theorem cofiberedProductTangentEquiv_toLinearMap (M : FGModuleCat.{w} k) :
    (cofiberedProductTangentEquiv h𝓕 h𝓖 M).toLinearMap = cofiberedProductTangentPair h𝓕 h𝓖 M :=
  rfl

/-- The map induced on tangent modules by a composite of `1`-morphisms is the composite of the
induced maps. -/
private theorem tangentMapAt_comp_apply
    {𝓐 : BasedCategory.{_, _} (ArtinianLocalAlgCat.{u, w, w} Λ k)}
    {𝓑 : BasedCategory.{_, _} (ArtinianLocalAlgCat.{u, w, w} Λ k)}
    {𝓒 : BasedCategory.{_, _} (ArtinianLocalAlgCat.{u, w, w} Λ k)}
    (h𝓐 : IsDeformationCategory.{u, w, w} 𝓐.p) (h𝓑 : IsDeformationCategory.{u, w, w} 𝓑.p)
    (h𝓒 : IsDeformationCategory.{u, w, w} 𝓒.p) (φ : 𝓐 ⥤ᵇ 𝓑) (χ : 𝓑 ⥤ᵇ 𝓒)
    (M : FGModuleCat.{w} k) (s : ↥(tangentModuleAt.{u, w, w} 𝓐 h𝓐 M)) :
    tangentMapAt.{u, w, w} h𝓐 h𝓒 (BasedFunctor.comp φ χ) M s =
      tangentMapAt.{u, w, w} h𝓑 h𝓒 χ M (tangentMapAt.{u, w, w} h𝓐 h𝓑 φ M s) := by
  obtain ⟨x, rfl⟩ := tangentClassAt_surjective.{u, w, w} 𝓐 h𝓐 M s
  rw [tangentMapAt_tangentClassAt.{u, w, w}, tangentMapAt_tangentClassAt.{u, w, w},
    tangentMapAt_tangentClassAt.{u, w, w}]
  rfl

/-- For morphisms `φ : 𝓗 → 𝓕` and `ψ : 𝓗 → 𝓖` over `𝒞_Λ`, the pair of the maps they induce on
tangent modules is the map induced by `(φ, ψ) : 𝓗 → 𝓕 × 𝓖` followed by the identification
`T(𝓕 × 𝓖) ≅ T𝓕 × T𝓖`. -/
theorem prod_tangentMapAt_eq_cofiberedProductTangentEquiv_comp
    (h𝓗 : IsDeformationCategory.{u, w, w} 𝓗.p) (φ : 𝓗 ⥤ᵇ 𝓕) (ψ : 𝓗 ⥤ᵇ 𝓖)
    (M : FGModuleCat.{w} k) :
    LinearMap.prod (tangentMapAt.{u, w, w} h𝓗 h𝓕 φ M) (tangentMapAt.{u, w, w} h𝓗 h𝓖 ψ M) =
      (cofiberedProductTangentEquiv h𝓕 h𝓖 M).toLinearMap ∘ₗ
        tangentMapAt.{u, w, w} h𝓗
            (isDeformationCategory_cofiberedProduct_of_isDeformationCategory_id h𝓕 h𝓖)
          (cofiberedProductLift φ ψ) M := by
  refine LinearMap.ext fun s => Prod.ext ?_ ?_
  · exact (tangentMapAt_comp_apply h𝓗
      (isDeformationCategory_cofiberedProduct_of_isDeformationCategory_id h𝓕 h𝓖) h𝓕
      (cofiberedProductLift φ ψ) (cofiberedProductFst 𝓕 𝓖) M s)
  · exact (tangentMapAt_comp_apply h𝓗
      (isDeformationCategory_cofiberedProduct_of_isDeformationCategory_id h𝓕 h𝓖) h𝓖
      (cofiberedProductLift φ ψ) (cofiberedProductSnd 𝓕 𝓖) M s)

end Tangent

/-! ### The infinitesimal automorphisms of the product -/

section Infinitesimal

variable (h𝓕 : IsDeformationCategory.{u, w, w} 𝓕.p) (h𝓖 : IsDeformationCategory.{u, w, w} 𝓖.p)
  {w₀ : (cofiberedProduct 𝓕 𝓖).obj}
  (PW : ChosenPushforwardsAt (cofiberedProduct 𝓕 𝓖).p w₀)
  (QF : ChosenPushforwardsAt 𝓕.p ((cofiberedProductFst 𝓕 𝓖).obj w₀))
  (QG : ChosenPushforwardsAt 𝓖.p ((cofiberedProductSnd 𝓕 𝓖).obj w₀))

/-- The map `Inf(𝓕 × 𝓖) → Inf(𝓕) × Inf(𝓖)` at a base point `w₀` of `𝓕 × 𝓖` and its two
components: the pair of the `k`-linear maps induced on infinitesimal automorphisms by the two
projections of the product. -/
def cofiberedProductInfPair :
    letI := naturalLocalizedTangentAddCommGroup PW
      (isDeformationCategory_cofiberedProduct_of_isDeformationCategory_id h𝓕 h𝓖).satisfiesRS
    letI := naturalLocalizedTangentModule PW
      (isDeformationCategory_cofiberedProduct_of_isDeformationCategory_id h𝓕 h𝓖).satisfiesRS
    letI := naturalLocalizedTangentAddCommGroup QF h𝓕.satisfiesRS
    letI := naturalLocalizedTangentModule QF h𝓕.satisfiesRS
    letI := naturalLocalizedTangentAddCommGroup QG h𝓖.satisfiesRS
    letI := naturalLocalizedTangentModule QG h𝓖.satisfiesRS
    localizedAutomorphismFunctorTangent PW →ₗ[k]
      localizedAutomorphismFunctorTangent QF × localizedAutomorphismFunctorTangent QG :=
  letI := naturalLocalizedTangentAddCommGroup PW
    (isDeformationCategory_cofiberedProduct_of_isDeformationCategory_id h𝓕 h𝓖).satisfiesRS
  letI := naturalLocalizedTangentModule PW
    (isDeformationCategory_cofiberedProduct_of_isDeformationCategory_id h𝓕 h𝓖).satisfiesRS
  letI := naturalLocalizedTangentAddCommGroup QF h𝓕.satisfiesRS
  letI := naturalLocalizedTangentModule QF h𝓕.satisfiesRS
  letI := naturalLocalizedTangentAddCommGroup QG h𝓖.satisfiesRS
  letI := naturalLocalizedTangentModule QG h𝓖.satisfiesRS
  LinearMap.prod
    (inducedInfinitesimalLinearMapOfEq (cofiberedProductFst 𝓕 𝓖).toFunctor
      (cofiberedProductFst 𝓕 𝓖).w
          (isDeformationCategory_cofiberedProduct_of_isDeformationCategory_id h𝓕 h𝓖).satisfiesRS
      h𝓕.satisfiesRS PW QF)
    (inducedInfinitesimalLinearMapOfEq (cofiberedProductSnd 𝓕 𝓖).toFunctor
      (cofiberedProductSnd 𝓕 𝓖).w
          (isDeformationCategory_cofiberedProduct_of_isDeformationCategory_id h𝓕 h𝓖).satisfiesRS
      h𝓖.satisfiesRS PW QG)

/-- **The infinitesimal automorphisms of a product are the products of those of the factors.**
The pair of the maps induced on infinitesimal automorphisms by the two projections of
`𝓕 × 𝓖` is bijective. It is injective because an arrow of the product is determined by its two
components. It is surjective because each induced map is conjugation by a vertical comparison
of chosen pushforwards: a pair of infinitesimal automorphisms of the components, conjugated back,
is a pair of vertical automorphisms of the two components of the chosen pushforward of `w₀`,
hence a vertical automorphism of it, and that automorphism is infinitesimal because the special
fibre of the predeformation category `𝓕 × 𝓖` is thin. -/
theorem bijective_cofiberedProductInfPair :
    letI := naturalLocalizedTangentAddCommGroup PW
      (isDeformationCategory_cofiberedProduct_of_isDeformationCategory_id h𝓕 h𝓖).satisfiesRS
    letI := naturalLocalizedTangentModule PW
      (isDeformationCategory_cofiberedProduct_of_isDeformationCategory_id h𝓕 h𝓖).satisfiesRS
    letI := naturalLocalizedTangentAddCommGroup QF h𝓕.satisfiesRS
    letI := naturalLocalizedTangentModule QF h𝓕.satisfiesRS
    letI := naturalLocalizedTangentAddCommGroup QG h𝓖.satisfiesRS
    letI := naturalLocalizedTangentModule QG h𝓖.satisfiesRS
    Function.Bijective (cofiberedProductInfPair h𝓕 h𝓖 PW QF QG) := by
  set hP := isDeformationCategory_cofiberedProduct_of_isDeformationCategory_id h𝓕 h𝓖
  let := naturalLocalizedTangentAddCommGroup PW hP.satisfiesRS
  let := naturalLocalizedTangentModule PW hP.satisfiesRS
  let := naturalLocalizedTangentAddCommGroup QF h𝓕.satisfiesRS
  let := naturalLocalizedTangentModule QF h𝓕.satisfiesRS
  let := naturalLocalizedTangentAddCommGroup QG h𝓖.satisfiesRS
  let := naturalLocalizedTangentModule QG h𝓖.satisfiesRS
  refine ⟨injective_prod_inducedInfinitesimalLinearMapOfEq
    (cofiberedProductFst 𝓕 𝓖).toFunctor (cofiberedProductSnd 𝓕 𝓖).toFunctor
    (cofiberedProductFst 𝓕 𝓖).w (cofiberedProductSnd 𝓕 𝓖).w hP.satisfiesRS
    h𝓕.satisfiesRS h𝓖.satisfiesRS PW QF QG
    (fun _ _ h₁ h₂ => TwoFibreProductOver.Hom.ext' h₁ h₂), ?_⟩
  rintro ⟨s, t⟩
  obtain ⟨H₁, hH₁, -, hconj₁⟩ := inducedInfinitesimalLinearMapOfEq_spec_iso
    (cofiberedProductFst 𝓕 𝓖).toFunctor (cofiberedProductFst 𝓕 𝓖).w hP.satisfiesRS
    h𝓕.satisfiesRS PW QF
  obtain ⟨H₂, hH₂, -, hconj₂⟩ := inducedInfinitesimalLinearMapOfEq_spec_iso
    (cofiberedProductSnd 𝓕 𝓖).toFunctor (cofiberedProductSnd 𝓕 𝓖).w hP.satisfiesRS
    h𝓖.satisfiesRS PW QG
  -- a pair of vertical automorphisms of the two components is, after conjugation, the pair of
  -- components of an automorphism
  have key {A : ArtinianLocalAlgCat.{u, w, w} Λ k} (W : (cofiberedProduct 𝓕 𝓖).p.Fiber A)
      {B₁ B₂ : ArtinianLocalAlgCat.{u, w, w} Λ k} {X₁ : 𝓕.obj} {X₂ : 𝓖.obj}
      (H₁ : X₁ ≅ (cofiberedProductFst 𝓕 𝓖).obj W.1) (a₁ : X₁ ≅ X₁)
      (hH₁ : 𝓕.p.IsHomLift (𝟙 B₁) H₁.hom) (ha₁ : 𝓕.p.IsHomLift (𝟙 B₁) a₁.hom)
      (H₂ : X₂ ≅ (cofiberedProductSnd 𝓕 𝓖).obj W.1) (a₂ : X₂ ≅ X₂)
      (hH₂ : 𝓖.p.IsHomLift (𝟙 B₂) H₂.hom) (ha₂ : 𝓖.p.IsHomLift (𝟙 B₂) a₂.hom) :
      ∃ γ : Aut W, (cofiberedProductFst 𝓕 𝓖).map γ.asIso.hom.val = H₁.inv ≫ a₁.hom ≫ H₁.hom ∧
        (cofiberedProductSnd 𝓕 𝓖).map γ.asIso.hom.val = H₂.inv ≫ a₂.hom ≫ H₂.hom := by
    have h₁ : 𝓕.p.IsHomLift (𝟙 B₁) (H₁.inv ≫ a₁.hom ≫ H₁.hom) := inferInstance
    have h₂ : 𝓖.p.IsHomLift (𝟙 B₂) (H₂.inv ≫ a₂.hom ≫ H₂.hom) := inferInstance
    exact ⟨Aut.of (cofiberedProductFiberIso W W
      (fiberIsoOfVertical _ _ (H₁.symm ≪≫ a₁ ≪≫ H₁) (isHomLift_id_of_base_eq
        ((IsHomLift.domain_eq 𝓕.p (𝟙 B₁) (H₁.inv ≫ a₁.hom ≫ H₁.hom)).symm.trans
          ((fiberFunctor (cofiberedProductFst 𝓕 𝓖) A).obj W).2) _ h₁))
      (fiberIsoOfVertical _ _ (H₂.symm ≪≫ a₂ ≪≫ H₂) (isHomLift_id_of_base_eq
        ((IsHomLift.domain_eq 𝓖.p (𝟙 B₂) (H₂.inv ≫ a₂.hom ≫ H₂.hom)).symm.trans
          ((fiberFunctor (cofiberedProductSnd 𝓕 𝓖) A).obj W).2) _ h₂))), rfl, rfl⟩
  obtain ⟨γ, hγ₁, hγ₂⟩ := key
    (PW.obj (dualNumbersUnder (p := (cofiberedProduct 𝓕 𝓖).p) (x := w₀)))
    H₁ ((Functor.Fiber.fiberInclusion (p := 𝓕.p)).mapIso (localizedTangentEquivKernel QF s).1.asIso)
    hH₁ (localizedTangentEquivKernel QF s).1.asIso.hom.2
    H₂ ((Functor.Fiber.fiberInclusion (p := 𝓖.p)).mapIso (localizedTangentEquivKernel QG t).1.asIso)
    hH₂ (localizedTangentEquivKernel QG t).1.asIso.hom.2
  have hmem : γ ∈ MonoidHom.ker (PW.transportAutHom
      (tangentReduction (p := (cofiberedProduct 𝓕 𝓖).p) (x := w₀))) := by
    rw [ker_transportAutHom_eq_top_of_isThin hP.predeformation.cofibered PW
      (isThin_specialFiber hP.predeformation)]
    exact Subgroup.mem_top _
  refine ⟨(localizedTangentEquivKernel PW).symm ⟨γ, hmem⟩, ?_⟩
  have hk := (localizedTangentEquivKernel PW).apply_symm_apply ⟨γ, hmem⟩
  refine Prod.ext ?_ ?_
  · change inducedInfinitesimalLinearMapOfEq (cofiberedProductFst 𝓕 𝓖).toFunctor
      (cofiberedProductFst 𝓕 𝓖).w hP.satisfiesRS h𝓕.satisfiesRS PW QF
      ((localizedTangentEquivKernel PW).symm ⟨γ, hmem⟩) = s
    apply (localizedTangentEquivKernel QF).injective
    refine Subtype.ext (Aut.ext (Iso.ext (Functor.Fiber.hom_ext
      ((cancel_mono H₁.hom).1 ((hconj₁ _).trans ?_)))))
    rw [hk]
    exact (congrArg (H₁.hom ≫ ·) hγ₁).trans (H₁.hom_inv_id_assoc _)
  · change inducedInfinitesimalLinearMapOfEq (cofiberedProductSnd 𝓕 𝓖).toFunctor
      (cofiberedProductSnd 𝓕 𝓖).w hP.satisfiesRS h𝓖.satisfiesRS PW QG
      ((localizedTangentEquivKernel PW).symm ⟨γ, hmem⟩) = t
    apply (localizedTangentEquivKernel QG).injective
    refine Subtype.ext (Aut.ext (Iso.ext (Functor.Fiber.hom_ext
      ((cancel_mono H₂.hom).1 ((hconj₂ _).trans ?_)))))
    rw [hk]
    exact (congrArg (H₂.hom ≫ ·) hγ₂).trans (H₂.hom_inv_id_assoc _)

/-- **`Inf(𝓕 × 𝓖) ≅ Inf(𝓕) × Inf(𝓖)`**: the infinitesimal automorphisms of the product of two
deformation categories at a base point `w₀` are `k`-linearly the product of the infinitesimal
automorphisms of the two factors at the components of `w₀`, by the pair of the maps induced by
the two projections. The `k`-structures are those of Tag 06JV,
`Deformation.naturalLocalizedTangentModule`, at the given choices of pushforwards. -/
def cofiberedProductInfEquiv :
    letI := naturalLocalizedTangentAddCommGroup PW
      (isDeformationCategory_cofiberedProduct_of_isDeformationCategory_id h𝓕 h𝓖).satisfiesRS
    letI := naturalLocalizedTangentModule PW
      (isDeformationCategory_cofiberedProduct_of_isDeformationCategory_id h𝓕 h𝓖).satisfiesRS
    letI := naturalLocalizedTangentAddCommGroup QF h𝓕.satisfiesRS
    letI := naturalLocalizedTangentModule QF h𝓕.satisfiesRS
    letI := naturalLocalizedTangentAddCommGroup QG h𝓖.satisfiesRS
    letI := naturalLocalizedTangentModule QG h𝓖.satisfiesRS
    localizedAutomorphismFunctorTangent PW ≃ₗ[k]
      localizedAutomorphismFunctorTangent QF × localizedAutomorphismFunctorTangent QG :=
  letI := naturalLocalizedTangentAddCommGroup PW
    (isDeformationCategory_cofiberedProduct_of_isDeformationCategory_id h𝓕 h𝓖).satisfiesRS
  letI := naturalLocalizedTangentModule PW
    (isDeformationCategory_cofiberedProduct_of_isDeformationCategory_id h𝓕 h𝓖).satisfiesRS
  letI := naturalLocalizedTangentAddCommGroup QF h𝓕.satisfiesRS
  letI := naturalLocalizedTangentModule QF h𝓕.satisfiesRS
  letI := naturalLocalizedTangentAddCommGroup QG h𝓖.satisfiesRS
  letI := naturalLocalizedTangentModule QG h𝓖.satisfiesRS
  LinearEquiv.ofBijective (cofiberedProductInfPair h𝓕 h𝓖 PW QF QG)
    (bijective_cofiberedProductInfPair h𝓕 h𝓖 PW QF QG)

/-- The underlying linear map of `cofiberedProductInfEquiv` is `cofiberedProductInfPair`. -/
theorem cofiberedProductInfEquiv_toLinearMap :
    letI := naturalLocalizedTangentAddCommGroup PW
      (isDeformationCategory_cofiberedProduct_of_isDeformationCategory_id h𝓕 h𝓖).satisfiesRS
    letI := naturalLocalizedTangentModule PW
      (isDeformationCategory_cofiberedProduct_of_isDeformationCategory_id h𝓕 h𝓖).satisfiesRS
    letI := naturalLocalizedTangentAddCommGroup QF h𝓕.satisfiesRS
    letI := naturalLocalizedTangentModule QF h𝓕.satisfiesRS
    letI := naturalLocalizedTangentAddCommGroup QG h𝓖.satisfiesRS
    letI := naturalLocalizedTangentModule QG h𝓖.satisfiesRS
    (cofiberedProductInfEquiv h𝓕 h𝓖 PW QF QG).toLinearMap =
      cofiberedProductInfPair h𝓕 h𝓖 PW QF QG :=
  rfl

/-- For morphisms `φ : 𝓗 → 𝓕` and `ψ : 𝓗 → 𝓖` over `𝒞_Λ`, the pair of the maps they induce on
infinitesimal automorphisms is the map induced by `(φ, ψ) : 𝓗 → 𝓕 × 𝓖` followed by the
identification `Inf(𝓕 × 𝓖) ≅ Inf(𝓕) × Inf(𝓖)`. -/
theorem prod_inducedInfinitesimalLinearMapOfEq_apply_eq_cofiberedProductInfEquiv
    (h𝓗 : SatisfiesRS 𝓗.p) (φ : 𝓗 ⥤ᵇ 𝓕) (ψ : 𝓗 ⥤ᵇ 𝓖) {x₀ : 𝓗.obj}
    (PH : ChosenPushforwardsAt 𝓗.p x₀)
    (PW : ChosenPushforwardsAt (cofiberedProduct 𝓕 𝓖).p ((cofiberedProductLift φ ψ).obj x₀))
    (QF : ChosenPushforwardsAt 𝓕.p (φ.obj x₀)) (QG : ChosenPushforwardsAt 𝓖.p (ψ.obj x₀)) :
    letI := naturalLocalizedTangentAddCommGroup PH h𝓗
    letI := naturalLocalizedTangentModule PH h𝓗
    letI := naturalLocalizedTangentAddCommGroup PW
      (isDeformationCategory_cofiberedProduct_of_isDeformationCategory_id h𝓕 h𝓖).satisfiesRS
    letI := naturalLocalizedTangentModule PW
      (isDeformationCategory_cofiberedProduct_of_isDeformationCategory_id h𝓕 h𝓖).satisfiesRS
    letI := naturalLocalizedTangentAddCommGroup QF h𝓕.satisfiesRS
    letI := naturalLocalizedTangentModule QF h𝓕.satisfiesRS
    letI := naturalLocalizedTangentAddCommGroup QG h𝓖.satisfiesRS
    letI := naturalLocalizedTangentModule QG h𝓖.satisfiesRS
    ∀ t : localizedAutomorphismFunctorTangent PH,
      LinearMap.prod
          (inducedInfinitesimalLinearMapOfEq φ.toFunctor φ.w h𝓗 h𝓕.satisfiesRS PH QF)
          (inducedInfinitesimalLinearMapOfEq ψ.toFunctor ψ.w h𝓗 h𝓖.satisfiesRS PH QG) t =
        cofiberedProductInfEquiv h𝓕 h𝓖 PW QF QG
          (inducedInfinitesimalLinearMapOfEq (cofiberedProductLift φ ψ).toFunctor
            (cofiberedProductLift φ ψ).w h𝓗
            (isDeformationCategory_cofiberedProduct_of_isDeformationCategory_id h𝓕 h𝓖).satisfiesRS
                PH PW t) := by
  intro t
  refine Prod.ext ?_ ?_
  · exact DFunLike.congr_fun (inducedInfinitesimalLinearMapOfEq_comp
      (cofiberedProductLift φ ψ).toFunctor (cofiberedProductFst 𝓕 𝓖).toFunctor
      (cofiberedProductLift φ ψ).w (cofiberedProductFst 𝓕 𝓖).w h𝓗
      (isDeformationCategory_cofiberedProduct_of_isDeformationCategory_id h𝓕 h𝓖).satisfiesRS
          h𝓕.satisfiesRS PH PW QF) t
  · exact DFunLike.congr_fun (inducedInfinitesimalLinearMapOfEq_comp
      (cofiberedProductLift φ ψ).toFunctor (cofiberedProductSnd 𝓕 𝓖).toFunctor
      (cofiberedProductLift φ ψ).w (cofiberedProductSnd 𝓕 𝓖).w h𝓗
      (isDeformationCategory_cofiberedProduct_of_isDeformationCategory_id h𝓕 h𝓖).satisfiesRS
          h𝓖.satisfiesRS PH PW QG) t

end Infinitesimal

end Deformation

end
