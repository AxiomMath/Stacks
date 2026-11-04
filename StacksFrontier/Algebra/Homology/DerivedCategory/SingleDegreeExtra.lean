module

public import StacksFrontier.Algebra.Homology.DerivedCategory.SingleDegree

/-!
# Morphisms into a complex concentrated in one degree

## Main results

* `DerivedCategory.bijective_homologyFunctor_map_comp_singleFunctorCompHomologyFunctorIso`: if the
  homology of `X` vanishes outside degree `n`, degree-`n` homology is a bijection
  `Hom(X, N[n]) → Hom(Hⁿ(X), N)`. Unlike
  `DerivedCategory.nonempty_iso_singleFunctor_homologyFunctor_of_isZero` this is about a *named*
  map, so it is usable where naturality matters: the bijection is `Hⁿ` itself, and the
  non-canonical isomorphism `X ≅ Hⁿ(X)[n]` appears only in its proof.
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits

universe w₁ v₁ u₁

namespace DerivedCategory

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasDerivedCategory.{w₁} C]

/-- **Morphisms into a complex concentrated in degree `n` are computed by degree-`n` homology.**
If the homology of `X` vanishes outside degree `n`, then taking degree-`n` homology is a bijection
from `Hom(X, N[n])` onto `Hom(Hⁿ(X), N)`.

The bijection is the one the hypotheses make canonical: no choice of isomorphism `X ≅ Hⁿ(X)[n]`
enters the statement, only `Hⁿ` and `singleFunctorCompHomologyFunctorIso`. One such isomorphism
is used in the proof, together with the full faithfulness of the single functor; the resulting
map differs from `Hⁿ` by composition with an automorphism of `Hⁿ(X)`, which is invertible. -/
public theorem bijective_homologyFunctor_map_comp_singleFunctorCompHomologyFunctorIso
    (X : DerivedCategory C) (n : ℤ)
    (hX : ∀ j : ℤ, j ≠ n → IsZero ((homologyFunctor C j).obj X)) (N : C) :
    Function.Bijective (fun u : X ⟶ (singleFunctor C n).obj N =>
      (homologyFunctor C n).map u ≫ ((singleFunctorCompHomologyFunctorIso C n).app N).hom) := by
  obtain ⟨e⟩ := X.nonempty_iso_singleFunctor_homologyFunctor_of_isZero n hX
  set M := (homologyFunctor C n).obj X with hM
  -- `ψ`, the automorphism of `Hⁿ(X)` by which the two descriptions differ
  set ψ : M ⟶ M := (homologyFunctor C n).map e.hom ≫
    ((singleFunctorCompHomologyFunctorIso C n).app M).hom with hψ
  have hψiso : IsIso ψ := by
    rw [hψ]
    infer_instance
  -- `ι`, the bijection `Hom(Hⁿ(X), N) ≃ Hom(X, N[n])`
  have hιbij : Function.Bijective
      (fun g : M ⟶ N => e.hom ≫ (singleFunctor C n).map g) := by
    have h₁ : Function.Bijective ((singleFunctor C n).map (X := M) (Y := N)) :=
      ⟨(singleFunctor C n).map_injective, (singleFunctor C n).map_surjective⟩
    exact ((isIso_iff_coyoneda_map_bijective e.hom).1 inferInstance _).comp h₁
  -- the composite is composition with `ψ`
  have hcomp : (fun u : X ⟶ (singleFunctor C n).obj N =>
        (homologyFunctor C n).map u ≫ ((singleFunctorCompHomologyFunctorIso C n).app N).hom) ∘
      (fun g : M ⟶ N => e.hom ≫ (singleFunctor C n).map g) = fun g : M ⟶ N => ψ ≫ g := by
    funext g
    have hnat := (singleFunctorCompHomologyFunctorIso C n).hom.naturality g
    simp only [Function.comp_apply, Functor.map_comp, assoc, hψ]
    exact congrArg ((homologyFunctor C n).map e.hom ≫ ·) hnat
  refine (Function.Bijective.of_comp_iff _ hιbij).1 ?_
  rw [hcomp]
  exact (isIso_iff_coyoneda_map_bijective ψ).1 hψiso N

end DerivedCategory

end
