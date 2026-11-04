module

public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraOverHomEquiv
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageSectionsGlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralClosureUniversal
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralUniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationInUniversalProperty

/-!
# The universal property of a relative normalization, read off its algebra

Let `f : Y ⟶ X` be a morphism of algebraic spaces over `S`, let `𝒪'` be the integral closure of
`𝒪_X` in `f_* 𝒪_Y`, and let `f = ν ∘ f'` be a factorization of `f` through a morphism
`ν : X' ⟶ X` which is affine and integral.  Suppose that `ν_* 𝒪_{X'}` is identified with `𝒪'`
in such a way that the map `ν_* 𝒪_{X'} ⟶ f_* 𝒪_Y` induced by `f'` becomes the inclusion
`𝒪' ⊂ f_* 𝒪_Y`.  This file proves that the factorization then has the universal property of
Stacks 0823: every factorization `f = π ∘ g` through an integral morphism `π : Z ⟶ X` of
algebraic spaces receives a unique `h : X' ⟶ Z` with `h ∘ f' = g` and `π ∘ h = ν`.

This is the source's proof of property (2) of Stacks 0823, with the relative spectrum of
Stacks 081V replaced by the mapping property the argument actually uses: a morphism over `X`
into an algebraic space affine over `X` is the same thing as a map of direct-image algebras in
the other direction (`AlgebraicGeometry.Space.overHomEquivPushforwardAlgebraHom`).

## Main results

* `AlgebraicGeometry.Space.isIntegral_pushforwardAlgebra_of_isIntegralHom`: the direct-image
  algebra of an integral morphism is integral.
* `AlgebraicGeometry.Space.isRelativeNormalization_of_pushforwardAlgebraMap_eq`: **the
  criterion.**  A factorization through an affine integral morphism whose algebra is the
  integral closure, the factorization inducing the inclusion, has the universal property of
  Stacks 0823.

## Implementation notes

**The proof is the source's.**  The algebra `ℬ = π_* 𝒪_Z` of a test object is integral, so the
map `χ : ℬ ⟶ f_* 𝒪_Y` induced by `g` factors through `𝒪'`, uniquely
(`AlgebraicGeometry.Space.AlgebraSheaf.existsUnique_hom_integralClosureSheaf`, the step the
source performs with Stacks 0820).  Composing with the identification `𝒪' ≅ ν_* 𝒪_{X'}` gives a
map `ℬ ⟶ ν_* 𝒪_{X'}`, which is induced by a morphism `h : X' ⟶ Z` over `X` because `ν` is
affine, hence representable.  The equation `h ∘ f' = g` holds after direct image, by
contravariant functoriality of `f ↦ f_* 𝒪`, and direct image is faithful on morphisms into `Z`;
and any other `h'` induces a factorization of `χ` through `𝒪'`, which is the first one by
uniqueness, so `h' = h` by faithfulness again.  Nothing is chosen except `h` itself, which is
pinned down by its direct-image map.

## References

* [Stacks Project, Tag 0823](https://stacks.math.columbia.edu/tag/0823)
* [Stacks Project, Tag 0820](https://stacks.math.columbia.edu/tag/0820)
* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
* [Stacks Project, Tag 03ZP](https://stacks.math.columbia.edu/tag/03ZP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The algebra of an integral morphism -/

/-- **The direct-image algebra of an integral morphism of algebraic spaces is integral.**  An
integral morphism is universally closed, by Stacks 0415, and the direct image of the structure
sheaf along a universally closed morphism is integral, by the first assertion of Stacks 0A0Q. -/
theorem isIntegral_pushforwardAlgebra_of_isIntegralHom {X Y : AlgebraicSpaces B S hS}
    (f : Y ⟶ X) (hf : IsIntegralHom B S hS f.hom) :
    (pushforwardAlgebra B S hS (Over.mk f)).IsIntegral :=
  isIntegral_pushforwardAlgebra_of_universallyClosed B S hS f
    ((isIntegralHom_iff_isAffineHom_and_universallyClosed B S hS Y.property X.property
      f.hom).1 hf).2

/-! ### The criterion -/

/-- **A factorization whose algebra is the integral closure has the universal property of
Stacks 0823.**

Let `f : Y ⟶ X` be a morphism of algebraic spaces, `X'` an algebraic space affine over `X` whose
structure morphism `ν` is integral, and `f' : Y ⟶ X'` a morphism over `X`.  If `ν_* 𝒪_{X'}` is
identified with the integral closure `𝒪'` of `𝒪_X` in `f_* 𝒪_Y` in such a way that the map
induced by `f'` is the inclusion `𝒪' ⊂ f_* 𝒪_Y`, then `f = ν ∘ f'` is a relative normalization:
every factorization `f = π ∘ g` through an integral morphism `π : Z ⟶ X` of algebraic spaces
receives a unique `h : X' ⟶ Z` with `h ∘ f' = g` and `π ∘ h = ν`. -/
theorem isRelativeNormalization_of_pushforwardAlgebraMap_eq {X Y : AlgebraicSpaces B S hS}
    (f : Y ⟶ X) (X' : AffineOver B S hS X) (hν : IsIntegralHom B S hS X'.obj.hom.hom)
    (f' : Over.mk f ⟶ X'.obj)
    (e : AlgebraSheaf.integralClosureSheaf (pushforwardAlgebra B S hS (Over.mk f)) ≅
      pushforwardAlgebra B S hS X'.obj)
    (he : e.hom ≫ pushforwardAlgebraMap B S hS f' =
      AlgebraSheaf.integralClosureInclusion (pushforwardAlgebra B S hS (Over.mk f))) :
    IsRelativeNormalization B S hS f.hom X'.obj.hom.hom f'.left.hom := by
  have hX' : yoneda.relativelyRepresentable X'.obj.hom.hom :=
    relativelyRepresentable_of_isAffineHom B S hS X'.obj.hom X'.property
  refine ⟨congrArg (fun k => k.hom) (Over.w f'), hν, ?_⟩
  intro Z hZ π hπ g hg
  let πs : (⟨Z, hZ⟩ : AlgebraicSpaces B S hS) ⟶ X := ObjectProperty.homMk π
  let ZA : AffineOver B S hS X := ⟨Over.mk πs, isAffineHom_of_isIntegralHom π hπ⟩
  let gs : Over.mk f ⟶ ZA.obj :=
    Over.homMk (ObjectProperty.homMk g) (ObjectProperty.hom_ext _ hg)
  obtain ⟨ψ, hψ, hψuniq⟩ := AlgebraSheaf.existsUnique_hom_integralClosureSheaf
    (pushforwardAlgebraMap B S hS gs) (isIntegral_pushforwardAlgebra_of_isIntegralHom B S hS πs hπ)
  obtain ⟨k, hk⟩ :=
    exists_pushforwardAlgebraMap_eq_of_relativelyRepresentable B S hS hX' ZA (ψ ≫ e.hom)
  have hfac : f' ≫ k = gs := eq_of_pushforwardAlgebraMap_eq B S hS ZA (by
    rw [pushforwardAlgebraMap_comp, hk, Category.assoc, he, hψ])
  refine ⟨k.left.hom, ⟨congrArg (fun m => m.left.hom) hfac,
    congrArg (fun m => m.hom) (Over.w k)⟩, ?_⟩
  rintro h ⟨h1, h2⟩
  let hO : X'.obj ⟶ ZA.obj := Over.homMk (ObjectProperty.homMk h) (ObjectProperty.hom_ext _ h2)
  have hfac' : f' ≫ hO = gs := Over.OverMorphism.ext (ObjectProperty.hom_ext _ h1)
  have hOk : hO = k := by
    refine eq_of_pushforwardAlgebraMap_eq_of_relativelyRepresentable B S hS hX' ZA ?_
    rw [hk, ← Iso.comp_inv_eq]
    refine hψuniq _ ?_
    beta_reduce
    rw [Category.assoc, ← he, Iso.inv_hom_id_assoc, ← pushforwardAlgebraMap_comp, hfac']
  exact congrArg (fun m => m.left.hom) hOk

end AlgebraicGeometry.Space

end
