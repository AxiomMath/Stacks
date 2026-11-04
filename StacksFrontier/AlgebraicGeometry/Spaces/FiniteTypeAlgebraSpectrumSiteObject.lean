module

public import StacksFrontier.AlgebraicGeometry.Spaces.ReesSpectrumSiteObject

/-!
# The spectrum of a finitely generated algebra over an affine object, as an object of the site

For an affine object `T` of the site with `A = Γ(T₀, ⊤)` and a finitely generated `A`-algebra `R`
(in the universe of the site), `Spec R ⟶ Spec A ≅ T₀` is of finite type, so `Spec R` lies in the
site as an object over `T`; an `A`-algebra map `R ⟶ R'` gives a morphism of the site over `T`.

## Main definitions

* `AlgebraicGeometry.Space.algebraSpectrumOver`: `Spec R` as an object of the site.
* `AlgebraicGeometry.Space.algebraSpectrumSiteHom`: its morphism to `T`.
* `AlgebraicGeometry.Space.algebraSpectrumSiteMap`: the morphism induced by an `A`-algebra map.

## References

* [Stacks Project, Tag 08AW](https://stacks.math.columbia.edu/tag/08AW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (T : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]

/-- The morphism of schemes `Spec R ⟶ T₀` for an `A`-algebra `R`, `A = Γ(T₀, ⊤)`. -/
def algebraSpectrumMap (R : Type u) [CommRing R]
    [Algebra Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) R] :
    Spec (.of R) ⟶ (BigFppfOver.toScheme B S hS).obj T :=
  Spec.map (CommRingCat.ofHom (algebraMap Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) R)) ≫
    ((BigFppfOver.toScheme B S hS).obj T).isoSpec.inv

/-- The morphism `Spec R ⟶ T₀` is quasi-compact. -/
instance (R : Type u) [CommRing R] [Algebra Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) R] :
    QuasiCompact (algebraSpectrumMap B S hS T R) := by
  unfold algebraSpectrumMap
  infer_instance

/-- For a finitely generated `A`-algebra `R`, the morphism `Spec R ⟶ T₀` is locally of finite
type. -/
instance (R : Type u) [CommRing R] [Algebra Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) R]
    [Algebra.FiniteType Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) R] :
    LocallyOfFiniteType (algebraSpectrumMap B S hS T R) := by
  have : (algebraMap Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) R).FiniteType :=
    RingHom.finiteType_algebraMap.mpr inferInstance
  have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom
      (algebraMap Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) R))) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr this
  unfold algebraSpectrumMap
  infer_instance

/-- **`Spec R` as an object of the site over `S`**, for a finitely generated `A`-algebra `R`. -/
def algebraSpectrumOver (R : Type u) [CommRing R]
    [Algebra Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) R]
    [Algebra.FiniteType Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) R] : BigFppfOver B S hS :=
  BigFppfOver.mk B S hS
    (Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact (algebraSpectrumMap B S hS T R)
      (show B.Contains ((BigFppfOver.toScheme B S hS).obj T) from T.left.property))
    (algebraSpectrumMap B S hS T R ≫ B.inclusion.map T.hom)

variable (R : Type u) [CommRing R] [Algebra Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) R]
  [Algebra.FiniteType Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) R]

/-- The underlying scheme of `algebraSpectrumOver B S hS T R` is `Spec R`. -/
@[simp]
theorem toScheme_obj_algebraSpectrumOver :
    (BigFppfOver.toScheme B S hS).obj (algebraSpectrumOver B S hS T R) = Spec (.of R) :=
  rfl

/-- The underlying scheme of `algebraSpectrumOver B S hS T R` is affine. -/
instance : IsAffine ((BigFppfOver.toScheme B S hS).obj (algebraSpectrumOver B S hS T R)) :=
  inferInstanceAs (IsAffine (Spec (.of R)))

/-- The morphism `Spec R ⟶ T` of the site. -/
def algebraSpectrumSiteHom : algebraSpectrumOver B S hS T R ⟶ T :=
  Over.homMk (ObjectProperty.homMk (algebraSpectrumMap B S hS T R))
    (by apply ObjectProperty.hom_ext; rfl)

/-- The morphism `Spec R' ⟶ Spec R` of the site over `T` induced by an `A`-algebra map
`φ : R →ₐ R'`. -/
def algebraSpectrumSiteMap (R' : Type u) [CommRing R']
    [Algebra Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) R']
    [Algebra.FiniteType Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) R']
    (φ : R →ₐ[Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)] R') :
    algebraSpectrumOver B S hS T R' ⟶ algebraSpectrumOver B S hS T R :=
  Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom φ.toRingHom)))
    (by
      apply ObjectProperty.hom_ext
      change Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (algebraSpectrumMap B S hS T R ≫
        B.inclusion.map T.hom) = algebraSpectrumMap B S hS T R' ≫ B.inclusion.map T.hom
      rw [← Category.assoc]
      congr 1
      rw [algebraSpectrumMap, algebraSpectrumMap, ← Category.assoc, ← Spec.map_comp]
      congr 2
      ext x
      exact φ.commutes x)

/-- The morphism `Spec R' ⟶ Spec R` induced by `φ : R →ₐ R'`, followed by `Spec R ⟶ T`, is the
morphism `Spec R' ⟶ T`. -/
theorem algebraSpectrumSiteMap_comp_siteHom (R' : Type u) [CommRing R']
    [Algebra Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) R']
    [Algebra.FiniteType Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) R']
    (φ : R →ₐ[Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)] R') :
    algebraSpectrumSiteMap B S hS T R R' φ ≫ algebraSpectrumSiteHom B S hS T R =
      algebraSpectrumSiteHom B S hS T R' :=
  Over.OverMorphism.ext (by apply ObjectProperty.hom_ext; exact
    (show Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ algebraSpectrumMap B S hS T R =
      algebraSpectrumMap B S hS T R' by
      rw [algebraSpectrumMap, algebraSpectrumMap, ← Category.assoc, ← Spec.map_comp]
      congr 2
      ext x
      exact φ.commutes x))

end AlgebraicGeometry.Space

end
