module

public import StacksFrontier.AlgebraicGeometry.Spaces.SpecQuotientOverAffineBase
public import Mathlib.RingTheory.ReesAlgebra
public import Mathlib.RingTheory.FiniteType

/-!
# The spectrum of the Rees algebra of an ideal, as an object of the site

Let `T` be an affine object of the big fppf site over `S` and `J` a finitely generated ideal of
`A = Γ(T, 𝒪_T)`. The Rees algebra `A[Jt] = ⨁_{n ≥ 0} Jⁿ` is a finitely generated `A`-algebra, so
its spectrum, mapped to `T` by `Spec A[Jt] ⟶ Spec A ≅ T`, is of finite type over `T` and lies in
the site over `S`.

## Main definitions

* `AlgebraicGeometry.Space.reesSpectrumMap`: the morphism of schemes `Spec A[Jt] ⟶ T₀`.
* `AlgebraicGeometry.Space.reesSpectrumOver`: `Spec A[Jt]` as an object of the site.
* `AlgebraicGeometry.Space.reesSpectrumSiteHom`: its morphism to `T`.

## Main results

* `AlgebraicGeometry.Space.isLocallyNoetherian_reesSpectrumOver`: its scheme is locally Noetherian
  when `A` is Noetherian.

## References

* [Stacks Project, Tag 08AW](https://stacks.math.columbia.edu/tag/08AW)
* [Stacks Project, Tag 02O8](https://stacks.math.columbia.edu/tag/02O8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable (T : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]

/-- The morphism of schemes `Spec A[Jt] ⟶ T₀` for an ideal `J` of `A = Γ(T₀, ⊤)`. -/
def reesSpectrumMap (J : Ideal Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)) :
    Spec (.of (reesAlgebra J)) ⟶ (BigFppfOver.toScheme B S hS).obj T :=
  Spec.map (CommRingCat.ofHom (algebraMap Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)
    (reesAlgebra J))) ≫ ((BigFppfOver.toScheme B S hS).obj T).isoSpec.inv

/-- The morphism `Spec A[Jt] ⟶ T₀` is quasi-compact. -/
instance (J : Ideal Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)) :
    QuasiCompact (reesSpectrumMap B S hS T J) := by
  unfold reesSpectrumMap
  infer_instance

/-- For a finitely generated ideal `J`, the morphism `Spec A[Jt] ⟶ T₀` is locally of finite
type. -/
theorem locallyOfFiniteType_reesSpectrumMap (J : Ideal Γ((BigFppfOver.toScheme B S hS).obj T, ⊤))
    (hJ : J.FG) : LocallyOfFiniteType (reesSpectrumMap B S hS T J) := by
  have hft : Algebra.FiniteType Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) (reesAlgebra J) :=
    (Subalgebra.fg_iff_finiteType _).mp (reesAlgebra.fg hJ)
  have : (algebraMap Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) (reesAlgebra J)).FiniteType :=
    RingHom.finiteType_algebraMap.mpr hft
  have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom
      (algebraMap Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) (reesAlgebra J)))) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr this
  unfold reesSpectrumMap
  infer_instance

/-- **`Spec A[Jt]` as an object of the site over `S`**, for a finitely generated ideal `J` of
`A = Γ(T₀, ⊤)`, with structure morphism `Spec A[Jt] ⟶ T₀ ⟶ S`. -/
def reesSpectrumOver (J : Ideal Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)) (hJ : J.FG) :
    BigFppfOver B S hS :=
  haveI := locallyOfFiniteType_reesSpectrumMap B S hS T J hJ
  BigFppfOver.mk B S hS
    (Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact (reesSpectrumMap B S hS T J)
      (show B.Contains ((BigFppfOver.toScheme B S hS).obj T) from T.left.property))
    (reesSpectrumMap B S hS T J ≫ B.inclusion.map T.hom)

/-- The underlying scheme of `reesSpectrumOver B S hS T J hJ` is `Spec A[Jt]`. -/
@[simp]
theorem toScheme_obj_reesSpectrumOver (J : Ideal Γ((BigFppfOver.toScheme B S hS).obj T, ⊤))
    (hJ : J.FG) :
    (BigFppfOver.toScheme B S hS).obj (reesSpectrumOver B S hS T J hJ) =
      Spec (.of (reesAlgebra J)) :=
  rfl

/-- The morphism `Spec A[Jt] ⟶ T` of the site. -/
def reesSpectrumSiteHom (J : Ideal Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)) (hJ : J.FG) :
    reesSpectrumOver B S hS T J hJ ⟶ T :=
  Over.homMk (ObjectProperty.homMk (reesSpectrumMap B S hS T J))
    (by apply ObjectProperty.hom_ext; rfl)

/-- The underlying morphism of schemes of `reesSpectrumSiteHom B S hS T J hJ` is
`reesSpectrumMap B S hS T J`. -/
theorem toScheme_map_reesSpectrumSiteHom (J : Ideal Γ((BigFppfOver.toScheme B S hS).obj T, ⊤))
    (hJ : J.FG) :
    (BigFppfOver.toScheme B S hS).map (reesSpectrumSiteHom B S hS T J hJ) =
      reesSpectrumMap B S hS T J :=
  rfl

/-- The underlying scheme of `reesSpectrumOver B S hS T J hJ` is affine. -/
instance (J : Ideal Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)) (hJ : J.FG) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj (reesSpectrumOver B S hS T J hJ)) :=
  inferInstanceAs (IsAffine (Spec (.of (reesAlgebra J))))

/-- If `A` is Noetherian, then the underlying scheme of `reesSpectrumOver B S hS T J hJ` is locally
Noetherian. -/
theorem isLocallyNoetherian_reesSpectrumOver
    [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)]
    (J : Ideal Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)) (hJ : J.FG) :
    IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj (reesSpectrumOver B S hS T J hJ)) := by
  exact inferInstanceAs (IsLocallyNoetherian (Spec (.of (reesAlgebra J))))

end AlgebraicGeometry.Space

end
