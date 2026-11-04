module

public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.ChartGlue.SpecSite
public import StacksFrontier.AlgebraicGeometry.Size.OpenCover

/-!
# An affine object over an affine object is a spectrum

Let `E` be an object of the big fppf site over `S` whose scheme is affine, with a morphism
`e : E ⟶ T'` to an affine object `T'`. Then `Γ(E, ⊤)` is an algebra over `A' = Γ(T', ⊤)`, its
spectrum belongs to the site, and `E` is isomorphic over `T'` to `specObj Γ(E, ⊤)`.

## Main definitions

* `AlgebraicGeometry.Space.ChartGlue.ringAlg`: the `A'`-algebra structure on `Γ(E, ⊤)`.
* `AlgebraicGeometry.Space.ChartGlue.specIso`: the isomorphism `specObj Γ(E, ⊤) ≅ E`.

## Main results

* `AlgebraicGeometry.Space.ChartGlue.specIso_hom_comp`: the isomorphism lies over `T'`.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space.ChartGlue

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (T' : BigFppfOver B S hS)
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T')]
  {E : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj E)] (e : E ⟶ T')

/-- The ring `Γ(E, ⊤)`. -/
abbrev ringE : Type u := Γ((BigFppfOver.toScheme B S hS).obj E, ⊤)

/-- The `A'`-algebra structure on `Γ(E, ⊤)` given by `e`. -/
abbrev ringAlg : Algebra (ringOf B S hS T') (ringE B S hS (E := E)) :=
  ((BigFppfOver.toScheme B S hS).map e).appTop.hom.toAlgebra

/-- The spectrum of `Γ(E, ⊤)` belongs to the site. -/
lemma contains_specRingE : B.Contains (Spec (CommRingCat.of (ringE B S hS (E := E)))) := by
  change (Spec Γ((BigFppfOver.toScheme B S hS).obj E, ⊤)).size < B.cutoff
  rw [← Scheme.size_congr ((BigFppfOver.toScheme B S hS).obj E).isoSpec]
  exact E.left.property

/-- The structure map of `Spec Γ(E, ⊤)` is `Spec Γ(E) ≅ E ⟶ T'`. -/
lemma isoSpec_inv_comp :
    letI := ringAlg B S hS T' e
    ((BigFppfOver.toScheme B S hS).obj E).isoSpec.inv ≫ (BigFppfOver.toScheme B S hS).map e =
      specStr B S hS T' (ringE B S hS (E := E)) := by
  let := ringAlg B S hS T' e
  exact (Scheme.isoSpec_inv_naturality ((BigFppfOver.toScheme B S hS).map e)).symm

/-- The morphism `Spec Γ(E, ⊤) ≅ E` lies over `S`. -/
lemma isoSpec_inv_over :
    letI := ringAlg B S hS T' e
    ((BigFppfOver.toScheme B S hS).obj E).isoSpec.inv ≫ B.inclusion.map E.hom =
      specStr B S hS T' (ringE B S hS (E := E)) ≫ B.inclusion.map T'.hom := by
  let := ringAlg B S hS T' e
  rw [← isoSpec_inv_comp B S hS T' e, Category.assoc, ← Over.w e, Functor.map_comp]
  rfl

/-- **The isomorphism `specObj Γ(E, ⊤) ≅ E`.** -/
def specIso :
    letI := ringAlg B S hS T' e
    specObj B S hS T' (ringE B S hS (E := E)) (contains_specRingE B S hS) ≅ E :=
  letI := ringAlg B S hS T' e
  { hom := Over.homMk (ObjectProperty.homMk ((BigFppfOver.toScheme B S hS).obj E).isoSpec.inv)
      (by
        apply ObjectProperty.hom_ext
        exact isoSpec_inv_over B S hS T' e)
    inv := BigFppfOver.homMk B S hS (contains_specRingE B S hS) _
      ((BigFppfOver.toScheme B S hS).obj E).isoSpec.hom (by
        rw [← isoSpec_inv_over B S hS T' e, Iso.hom_inv_id_assoc])
    hom_inv_id := (BigFppfOver.toScheme B S hS).map_injective
      ((BigFppfOver.toScheme B S hS).obj E).isoSpec.inv_hom_id
    inv_hom_id := (BigFppfOver.toScheme B S hS).map_injective
      ((BigFppfOver.toScheme B S hS).obj E).isoSpec.hom_inv_id }

/-- The underlying morphism of schemes of `specIso` is the inverse of `E.isoSpec`. -/
lemma toScheme_map_specIso_hom :
    letI := ringAlg B S hS T' e
    (BigFppfOver.toScheme B S hS).map (specIso B S hS T' e).hom =
      ((BigFppfOver.toScheme B S hS).obj E).isoSpec.inv := rfl

/-- The isomorphism `specIso` lies over `T'`. -/
lemma specIso_hom_comp :
    letI := ringAlg B S hS T' e
    (specIso B S hS T' e).hom ≫ e = specToT B S hS T' _ (contains_specRingE B S hS) :=
  let := ringAlg B S hS T' e
  (BigFppfOver.toScheme B S hS).map_injective (isoSpec_inv_comp B S hS T' e)

section Naturality

variable {E₁ E₂ : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj E₁)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj E₂)] (e₁ : E₁ ⟶ T') (e₂ : E₂ ⟶ T')
  (h : E₁ ⟶ E₂) (he : h ≫ e₂ = e₁)

/-- The algebra map `Γ(E₂) → Γ(E₁)` of a morphism over `T'`. -/
def homRing : letI := ringAlg B S hS T' e₁; letI := ringAlg B S hS T' e₂
    ringE B S hS (E := E₂) →ₐ[ringOf B S hS T'] ringE B S hS (E := E₁) :=
  letI := ringAlg B S hS T' e₁; letI := ringAlg B S hS T' e₂
  { toRingHom := ((BigFppfOver.toScheme B S hS).map h).appTop.hom
    commutes' := fun r ↦ by
      change ((BigFppfOver.toScheme B S hS).map h).appTop.hom
        (((BigFppfOver.toScheme B S hS).map e₂).appTop.hom r) =
          ((BigFppfOver.toScheme B S hS).map e₁).appTop.hom r
      rw [← he, Functor.map_comp, Scheme.Hom.comp_appTop]
      rfl }

include he in
/-- **Naturality of `specIso`.** -/
lemma specMap_homRing_comp :
    letI := ringAlg B S hS T' e₁; letI := ringAlg B S hS T' e₂
    specMap B S hS T' (contains_specRingE B S hS (E := E₂)) (contains_specRingE B S hS (E := E₁))
        (homRing B S hS T' e₁ e₂ h he) ≫ (specIso B S hS T' e₂).hom =
      (specIso B S hS T' e₁).hom ≫ h := by
  let := ringAlg B S hS T' e₁
  let := ringAlg B S hS T' e₂
  apply (BigFppfOver.toScheme B S hS).map_injective
  change Spec.map (((BigFppfOver.toScheme B S hS).map h).appTop) ≫
      ((BigFppfOver.toScheme B S hS).obj E₂).isoSpec.inv =
    ((BigFppfOver.toScheme B S hS).obj E₁).isoSpec.inv ≫ (BigFppfOver.toScheme B S hS).map h
  exact Scheme.isoSpec_inv_naturality ((BigFppfOver.toScheme B S hS).map h)

end Naturality

end AlgebraicGeometry.Space.ChartGlue

end
